module

-- separate module: the body's proof, apart from the arithmetic of its result
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.CopyOut
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Mask
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.PcCall
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Time
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-! ### `Bignum.X86.PrivPre.PrimesCall`, which this module and modules that import it used -/

section

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

/-- `primes`' input: `R² mod n` in `pre`, after `n`. -/
abbrev inV (s : State) : BitVec 32 := arg s 0 + BitVec.ofNat 32 (8 * Spec.Rsa.modulusWords (arg s 3).toNat)

/-- The arguments of `primes`. -/
def primesVal (s : State) : Nat → BitVec 32
  | 0 => arg s 0
  | 1 => arg s 3
  | 2 => arg s 2
  | 3 => arg s 3
  | 4 => inV s
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

theorem preLen_ge (A : PPABI s) :
    16 * Spec.Rsa.modulusWords (arg s 3).toNat ≤ (arg s 1).toNat * 8 := by
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords] at hl
  omega_using [hl]

theorem inV_toNat (A : PPABI s) : (inV s).toNat = (arg s 0).toNat + 8 * Spec.Rsa.modulusWords (arg s 3).toNat := by
  have pb := A.preBound
  obtain pl := preLen_ge A
  simp only [inV, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 8 * Spec.Rsa.modulusWords (arg s 3).toNat) (by omega_using [pb, pl]), Nat.mod_eq_of_lt (by omega_using [pb, pl])]

theorem inV_ptr (A : PPABI s) :
    (inV s).setWidth 64 = argumentPointer s 0 + BitVec.ofNat 64 (8 * Spec.Rsa.modulusWords (arg s 3).toNat) := by
  have pb := A.preBound
  obtain pl := preLen_ge A
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, inV_toNat A]
  simp only [argumentPointer, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := (arg s 0).isLt
  omega_using []

/-- The input lies in `pre`, after `n`'s values' first `n_len` bytes. -/
theorem in_sub (A : PPABI s) : Region.Sub ⟨(inV s).setWidth 64, (arg s 3).toNat⟩ (preR s) := by
  obtain pl := preLen_ge A
  have := A.lengths
  simp only [Spec.Rsa.lenValid, Spec.Rsa.modulusWords] at this pl
  rw [inV_ptr A]
  exact Offset.sub_base _ (by simp only [Spec.Rsa.modulusWords]; omega_using [pl])

theorem in_out (A : PPABI s) :
    Region.Disjoint ⟨(inV s).setWidth 64, (arg s 3).toNat⟩ ⟨argumentPointer s 0, (arg s 3).toNat⟩ := by
  have := A.preBound
  obtain pl := preLen_ge A
  rw [inV_ptr A]
  exact Offset.disjoint_base _ (by simp only [Spec.Rsa.modulusWords]; omega_using []) (by omega_using [pl])

/-- `inV` to argument 4. -/
theorem inputArg_ok {is : List Instr} {Q : State → Prop} (A : PPABI s) (B : Body s t)
    (k : ∀ u, Body s u → Keeps [.eax] t u → Frame [argR s 4] t.mem u.mem →
      u.mem.readW (slot s (4 * 4)) 32 = inV s → WP isa (.block is) u Q) :
    WP isa (.block (Impl.Bignum.X86.PrivPre.inputArg ++ is)) t Q := by
  have pb := A.preBound
  obtain pl := preLen_ge A
  simp only [Impl.Bignum.X86.PrivPre.inputArg, Impl.Bignum.X86.PrivPre.shl, List.cons_append, List.nil_append]
  refine wp_movS (B.readArg A (by decide)) fun u₁ U₁ _ => wp_addi fun u₂ U₂ => wp_shr (by decide)
    fun u₃ U₃ _ => wp_add fun u₄ U₄ _ => wp_add fun u₅ U₅ _ => wp_add fun u₆ U₆ _ => ?_
  obtain K₆ : Keeps [.eax] t u₆ :=
    ⟨fun r hr => by
      obtain hr' : r ≠ .eax := by simpa using hr
      rw [U₆.other _ hr', U₅.other _ hr', U₄.other _ hr', U₃.other _ hr', U₂.other _ hr', U₁.other _ hr'],
      by rw [U₆.rd, U₅.rd, U₄.rd, U₃.rd, U₂.rd, U₁.rd], by rw [U₆.wr, U₅.wr, U₄.wr, U₃.wr, U₂.wr, U₁.wr]⟩
  obtain M₆ : u₆.mem = t.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  obtain B₆ : Body s u₆ := B.next (K₆.1 _ (by decide)) K₆.2.1 K₆.2.2 (by rw [M₆]; exact Frame.refl _ _)
  refine wp_addS (B₆.readArg A (by decide)) fun u₇ U₇ _ => ?_
  obtain K₇ : Keeps [.eax] t u₇ := K₆.trans (U₇.keeps.mono (by decide))
  obtain M₇ : u₇.mem = t.mem := by rw [U₇.mem, M₆]
  obtain B₇ : Body s u₇ := B.next (K₇.1 _ (by decide)) K₇.2.1 K₇.2.2 (by rw [M₇]; exact Frame.refl _ _)
  obtain v₇ : u₇.gpr .eax = inV s := by
    have l := A.lengths
    simp only [Spec.Rsa.lenValid] at l
    obtain hw : ((arg s 3 + 7) >>> 3).toNat = Spec.Rsa.modulusWords (arg s 3).toNat := by
      simp only [Spec.Rsa.modulusWords, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [show (7 : BitVec 32).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := (arg s 3).toNat + 7) (by omega_using [l])]
    rw [U₇.gpr, U₆.gpr, U₅.gpr, U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [inV_toNat A]
    simp only [BitVec.toNat_add, hw]
    have := (arg s 0).isLt
    simp only [Spec.Rsa.modulusWords] at pl ⊢
    omega_using [pb, pl]
  refine wp_slot A B₇ (d := 16) (by decide) fun u₈ B₈ M₈ => k u₈ B₈ ?_ ?_ ?_
  · exact ⟨fun r hr => by rw [M₈.gpr]; exact K₇.1 r hr, by rw [M₈.rd, K₇.2.1], by rw [M₈.wr, K₇.2.2]⟩
  · rw [M₈.mem, M₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [M₈.mem, Mem.readW_writeW_self32, v₇]

theorem primesArgs_ok (A : PPABI s) (B : Body s t) :
    WP isa (.block primesArgs) t fun u => Body s u ∧ Keeps [.eax] t u ∧
      Frame [⟨slot s 0, 84⟩] t.mem u.mem ∧ u.mem.readW (slot s 80) 32 = t.gpr .eax ∧
      ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j := by
  rw [show primesArgs = .store (stackAt statusOffset) .eax ::
    (copies primesPairs ++ (Impl.Bignum.X86.PrivPre.inputArg ++ [])) by simp [primesArgs]]
  refine wp_slot A B (d := 80) (by decide) fun u₀ B₀ M₀ => ?_
  refine wp_copies A primesPairs B₀ (by decide) (by decide) fun u₁ B₁ K₁ F₁ V₁ => ?_
  refine inputArg_ok A B₁ fun u B' K₂ F₂ V₂ => WP.block_nil ?_
  obtain Fs : Frame ((primesPairs.map fun p => argR s p.2) ++ [argR s 4]) u₀.mem u.mem :=
    (F₁.mono fun r hr => List.mem_append_left _ hr).trans (F₂.mono fun r hr => List.mem_append_right _ hr)
  obtain V : ∀ p ∈ primesPairs, u.mem.readW (slot s (4 * p.2)) 32 = arg s p.1 := fun p hp => by
    rw [← V₁ p hp]
    refine F₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    obtain rfl := List.mem_singleton.mp hr
    obtain h17 : p.2 < 18 ∧ p.2 ≠ 4 := by revert hp; generalize p = q; decide +revert
    simp only [argR, slot]
    exact Offset.disjoint _ (by omega_using [h17]) (by omega_using [h17]) (by omega_using [])
  have M₁ := M₀
  obtain K : Keeps [.eax] u₀ u := K₁.trans K₂
  refine ⟨B', ⟨fun r hr => by rw [K.1 r hr, M₁.gpr], by rw [K.2.1, M₁.rd], by rw [K.2.2, M₁.wr]⟩, ?_, ?_, ?_⟩
  · have sub : ∀ p ∈ primesPairs, Region.Sub (argR s p.2) ⟨slot s 0, 84⟩ := fun p hp => by
      have := (List.mem_map_of_mem (f := Prod.snd) hp)
      obtain h17 : p.2 < 18 := by revert this; generalize p.2 = j; decide +revert
      simp only [argR, slot]
      exact Offset.sub _ (by omega_using []) (by omega_using [h17])
    refine (?_ : Frame [⟨slot s 0, 84⟩] t.mem u₀.mem).trans (Fs.sub fun r hr => ?_)
    · rw [M₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using []))
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        exact ⟨_, List.mem_singleton_self _, sub p hp⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_singleton_self _, by simp only [argR, slot]; exact Offset.sub _ (by omega_using []) (by omega_using [])⟩
  · rw [Fs.readW (r := ⟨slot s 80, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), M₁.mem,
      Mem.readW_writeW_self32]
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      have := (List.mem_map_of_mem (f := Prod.snd) hp)
      obtain h17 : p.2 < 18 := by revert this; generalize p.2 = j; decide +revert
      exact Offset.disjoint _ (by omega_using [h17]) (by omega_using []) (by omega_using [h17])
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  · intro j hj
    match j, hj with
    | 0, _ =>
      obtain v := V (0, 0) (by decide)
      simp only at v
      rw [v]; rfl
    | 1, _ =>
      obtain v := V (3, 1) (by decide)
      simp only at v
      rw [v]; rfl
    | 2, _ =>
      obtain v := V (2, 2) (by decide)
      simp only at v
      rw [v]; rfl
    | 3, _ =>
      obtain v := V (3, 3) (by decide)
      simp only at v
      rw [v]; rfl
    | 4, _ => rw [V₂]; rfl
    | 5, _ =>
      obtain v := V (3, 5) (by decide)
      simp only at v
      rw [v]; rfl
    | 6, _ =>
      obtain v := V (4, 6) (by decide)
      simp only at v
      rw [v]; rfl
    | 7, _ =>
      obtain v := V (5, 7) (by decide)
      simp only at v
      rw [v]; rfl
    | 8, _ =>
      obtain v := V (6, 8) (by decide)
      simp only at v
      rw [v]; rfl
    | 9, _ =>
      obtain v := V (7, 9) (by decide)
      simp only at v
      rw [v]; rfl
    | 10, _ =>
      obtain v := V (4, 10) (by decide)
      simp only at v
      rw [v]; rfl
    | 11, _ =>
      obtain v := V (5, 11) (by decide)
      simp only at v
      rw [v]; rfl
    | 12, _ =>
      obtain v := V (6, 12) (by decide)
      simp only at v
      rw [v]; rfl
    | 13, _ =>
      obtain v := V (7, 13) (by decide)
      simp only at v
      rw [v]; rfl
    | 14, _ =>
      obtain v := V (4, 14) (by decide)
      simp only at v
      rw [v]; rfl
    | 15, _ =>
      obtain v := V (5, 15) (by decide)
      simp only at v
      rw [v]; rfl
    | 16, _ =>
      obtain v := V (8, 16) (by decide)
      simp only at v
      rw [v]; rfl
    | 17, _ =>
      obtain v := V (9, 17) (by decide)
      simp only at v
      rw [v]; rfl
    | _ + 18, h => omega

def prRd (s : State) : List Region :=
  [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨(inV s).setWidth 64, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩]
def prWr (s : State) : List Region :=
  [⟨argumentPointer s 0, (arg s 3).toNat⟩, wsR s, ⟨slot s 0, 72⟩]

theorem out_sub (A : PPABI s) : Region.Sub ⟨argumentPointer s 0, (arg s 3).toNat⟩ (preR s) := by
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
  exact Region.sub_prefix (by omega_using [hl])

theorem pr_pre (A : PPABI s) (B : Body s u) (V : ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j) :
    (Proof.Rsa.privateCrtContract abi 96).pre (u.callEntry.withRegions (prRd s) (prWr s)) := by
  obtain hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
    rw [callee_arg A B hj]; exact V j hj
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
  obtain os := out_sub A
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
  obtain o_n := A.preN.sub_left os
  obtain o_p := A.preP.sub_left os
  obtain o_q := A.preQ.sub_left os
  obtain o_w := A.preWs.sub_left os
  have n_w := A.nWs
  have p_w := A.pWs
  have q_w := A.qWs
  obtain o_a := (top_apart (d := 100) (n := 72) (by decide) (A.belowPre.sub_right os)).symm
  obtain n_a := (top_apart (d := 100) (n := 72) (by decide) A.belowN).symm
  obtain p_a := (top_apart (d := 100) (n := 72) (by decide) A.belowP).symm
  obtain q_a := (top_apart (d := 100) (n := 72) (by decide) A.belowQ).symm
  obtain w_a := (top_apart (d := 100) (n := 72) (by decide) A.belowWs).symm
  obtain r_o := top_apart (d := 96) (n := 4) (by decide) (A.belowPre.sub_right os)
  obtain r_n := top_apart (d := 96) (n := 4) (by decide) A.belowN
  obtain r_p := top_apart (d := 96) (n := 4) (by decide) A.belowP
  obtain r_q := top_apart (d := 96) (n := 4) (by decide) A.belowQ
  obtain r_w := top_apart (d := 96) (n := 4) (by decide) A.belowWs
  obtain r_a : (⟨bot s + BitVec.ofNat 64 96, 4⟩ : Region).Disjoint ⟨slot s 0, 72⟩ :=
    Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain bs : Region.Sub ⟨bot s, 96⟩ (topR s) := Region.sub_prefix (by simp [stackBytes])
  obtain b_o := (A.belowPre.sub_right os).sub_left bs
  obtain b_n := A.belowN.sub_left bs
  obtain b_p := A.belowP.sub_left bs
  obtain b_q := A.belowQ.sub_left bs
  obtain b_w := A.belowWs.sub_left bs
  obtain b_a : (⟨bot s, 96⟩ : Region).Disjoint ⟨slot s 0, 72⟩ := Offset.base_disjoint _ (by omega_using []) (by omega_using [])
  obtain is := in_sub A
  obtain i_o := in_out A
  obtain o_i := (in_out A).symm
  obtain i_w := A.preWs.sub_left is
  obtain i_a := (top_apart (d := 100) (n := 72) (by decide) (A.belowPre.sub_right is)).symm
  obtain r_i := top_apart (d := 96) (n := 4) (by decide) (A.belowPre.sub_right is)
  obtain b_i := (A.belowPre.sub_right is).sub_left bs
  obtain ib : (inV s).toNat + (arg s 3).toNat ≤ 2 ^ 32 := by
    obtain pl := preLen_ge A
    rw [inV_toNat A]; simp only [Spec.Rsa.modulusWords] at pl ⊢; omega_using [hl, pb]
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
  obtain hi := List.mem_range.mp hi
  rw [(callee_mem A B).bytes (R := ⟨a, n⟩) (fun r hr => ?_) (by simp; omega_using [hn]) hi]
  · exact B.frame.bytes (R := ⟨a, n⟩) hR (by simp; omega_using [hn]) hi
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
def PrOut (s : State) (X : Nat) (v : State) : Prop :=
  v.gpr .eax = BitVec.ofNat 32 (decide (valueAt s 4 * valueAt s 6 = valueAt s 2)).toNat ∧
  (X % CrtRt.safeM (valueAt s 4) = 2 ^ fixB (arg s 3).toNat % CrtRt.safeM (valueAt s 4) →
    val32 v.mem (argumentPointer s 8) (CrtRt.lo (arg s 3).toNat (.slot .wide 16))
        (2 * Spec.Rsa.primeWords (arg s 5).toNat) =
      2 ^ r2Exp (arg s 5).toNat % CrtRt.safeM (valueAt s 4)) ∧
  (X % CrtRt.safeM (valueAt s 6) = 2 ^ fixB (arg s 3).toNat % CrtRt.safeM (valueAt s 6) →
    val32 v.mem (argumentPointer s 8) (CrtRt.lo (arg s 3).toNat (.slot .wide 17))
        (2 * Spec.Rsa.primeWords (arg s 7).toNat) =
      2 ^ r2Exp (arg s 7).toNat % CrtRt.safeM (valueAt s 6))

/-- `x` as `primes` reads it: `pre`'s `n_len` bytes after `n`. -/
abbrev xPre (s : State) (m : Mem) : Nat := (m.read ((inV s).setWidth 64) (arg s 3).toNat).toNat

theorem pr_covers (A : PPABI s) (B : Body s u) :
    Covers (prRd s ++ prWr s) (u.rd ++ u.wr) ∧ Covers (prWr s) u.wr := by
  obtain cw : Covers (prWr s) u.wr := by
    rw [B.wr, A.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [prWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hl := A.preLength
      simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
      exact Covers.one ⟨preR s, by simp, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_using [hl]⟩
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · exact Covers.one ⟨frameR s, by simp, by
        rw [frame_base A]; exact Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [])⟩
  obtain cr : Covers (prRd s ++ prWr s) (u.rd ++ u.wr) := by
    refine Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right cw)
    simp only [prRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain pl := preLen_ge A
    obtain rdC : ∀ r ∈ s.rd, Covers [r] (u.rd ++ u.wr) := fun r h =>
      Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr', B.rd]; exact h)
    obtain inC : Covers [⟨(inV s).setWidth 64, (arg s 3).toNat⟩] (u.rd ++ u.wr) := by
      refine Covers.right (Covers.of_sub fun r' hr' => ⟨preR s, ?_, 8 * Spec.Rsa.modulusWords (arg s 3).toNat, ?_, ?_⟩)
      · rw [B.wr, A.wr]; simp
      · rw [List.mem_singleton.mp hr']; exact inV_ptr A
      · rw [List.mem_singleton.mp hr']
        have := A.lengths
        simp only [Spec.Rsa.lenValid, Spec.Rsa.modulusWords] at this pl ⊢
        omega_using [pl]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rdC _ (by rw [A.rd]; simp)
    · exact inC
    all_goals exact rdC _ (by rw [A.rd]; simp)
  exact ⟨cr, cw⟩

theorem pr_call {prName : String} (st : stackUse primes ≤ 96) (ns : NoSp primes)
    (A : PPABI s) (B : Body s u) (V : ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j) :
    WP isa (.call prName primes) u fun v => Body s v ∧ Keeps [.eax, .ecx, .edx] u v ∧
      Frame [wsR s, ⟨bot s, 100⟩] u.mem v.mem ∧ PrOut s (xPre s u.mem) v := by
  obtain os := out_sub A
  obtain argsSub : Region.Sub ⟨slot s 0, 72⟩ (frameR s) := by
    rw [frame_base A]; exact Offset.sub _ (by omega_using []) (by omega_using [])
  obtain ⟨cr, cw⟩ := pr_covers A B
  refine WP.mono (body_call primes_verified.1 st ns A B (pr_pre A B V) cr cw fun r hr => ?_)
    fun v ⟨Bv, K, F, w, M, G, post⟩ => ⟨Bv, K, ?_, ?_⟩
  · simp only [prWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨preR s, by simp, os⟩
    · exact ⟨wsR s, by simp, fun _ h => h⟩
    · exact ⟨topR s, by simp, Offset.sub_base _ (by simp [stackBytes])⟩
  · have hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
      rw [callee_arg A B hj]; exact V j hj
    obtain ⟨-, -, -, PF⟩ := post
    obtain ws : (⟨argumentPointer (u.callEntry.withRegions (prRd s) (prWr s)) 16,
        (arg (u.callEntry.withRegions (prRd s) (prWr s)) 17).toNat * 8⟩ : Region) = wsR s := by
      simp only [argumentPointer, hv 16 (by decide), hv 17 (by decide), primesVal]
    rw [ws, M] at PF
    obtain bl : Region.Sub (below ((u.callEntry.withRegions (prRd s) (prWr s)).gpr .esp) 96) ⟨bot s, 100⟩ := by
      rw [State.withRegions_gpr, State.callEntry_esp]
      have l := A.stackLow
      simp only [stackBytes] at l
      obtain e : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 96 := by
        rw [B.sp, sub_toNat (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega_using [l])]; rfl
      exact fun a h => below_frame A B (Nat.le_refl _) a
        (below_inner (sp := u.gpr .esp) (a := 96) (b := 100) (k := 4) (by decide) (by omega_using [l, e]) a h)
    refine ((callee_mem A B).sub fun r hr => ?_).trans (PF.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨bot s, 100⟩, by simp, Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wsR s, by simp, fun _ h => h⟩
      · exact ⟨⟨bot s, 100⟩, by simp, bl⟩
  · have hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
      rw [callee_arg A B hj]; exact V j hj
    obtain cv : ∀ {i a : Nat}, arg (u.callEntry.withRegions (prRd s) (prWr s)) i = arg s a →
        arg (u.callEntry.withRegions (prRd s) (prWr s)) (i + 1) = arg s (a + 1) →
        (∀ r ∈ bodyW s, (⟨argumentPointer s a, (arg s (a + 1)).toNat⟩ : Region).Disjoint r) →
        Crt.componentValue (u.callEntry.withRegions (prRd s) (prWr s)).mem
          (arg (u.callEntry.withRegions (prRd s) (prWr s))) i = valueAt s a := by
      intro i a h₁ h₂ hR
      unfold Crt.componentValue
      rw [h₁, h₂]
      exact congrArg _ (callee_bytes A B hR (arg s (a + 1)).isLt)
    obtain c2 := cv (i := 2) (a := 2) (hv 2 (by decide)) (hv 3 (by decide)) (n_apart A)
    obtain c6 := cv (i := 6) (a := 4) (hv 6 (by decide)) (hv 7 (by decide)) (p_apart A)
    obtain c8 := cv (i := 8) (a := 6) (hv 8 (by decide)) (hv 9 (by decide)) (q_apart A)
    obtain ⟨Pe, P16, P17, -⟩ := post
    rw [c2, c6, c8] at Pe
    rw [c6] at P16
    rw [c8] at P17
    simp only [argumentPointer, hv 16 (by decide), hv 3 (by decide), hv 7 (by decide), hv 9 (by decide),
      primesVal] at P16 P17
    rw [M] at P16 P17
    obtain xe : xIn (u.callEntry.withRegions (prRd s) (prWr s)).mem (arg (u.callEntry.withRegions (prRd s) (prWr s)))
        (arg s 3).toNat = xPre s u.mem := by
      simp only [xIn, byteAddr, hv 4 (by decide), primesVal]
      congr 1
      refine (callee_mem A B).read (r := ⟨(inV s).setWidth 64, (arg s 3).toNat⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by have := (arg s 3).isLt; omega_using [])
      obtain rfl := List.mem_singleton.mp hr
      exact (top_apart (d := 96) (n := 4) (by decide) (A.belowPre.sub_right (in_sub A))).symm
    rw [xe] at P16 P17
    exact ⟨by rw [← G .eax (by decide)]; exact Pe, P16, P17⟩


end
end VG.Proof.Bignum.X86.PrivPre

end

end

/-! # `vg_rsa_private_precompute` on x86: its body

From the frame's allocation, the body leaves `eax` the result
`st = p q = n ∧ n valid` (`stBit`), and `pre` the values it computed
(`PreVals`: `n`'s, if valid, `R_p² mod p'` and `R_q² mod q'` for the safe
factors `p'`, `q'`), each byte and-ed with the mask's (`body_ok`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (body statusOffset stackAt primes)

/-- `n`'s bytes. -/
abbrev nBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat

/-- The result of `vg_rsa_public_precompute`. -/
def pcBit (s : State) : BitVec 32 :=
  match Spec.Rsa.publicPrecompute (nBytes s) with
  | some _ => 1
  | none => 0

/-- The result of `primes`. -/
def prBit (s : State) : BitVec 32 := BitVec.ofNat 32 (decide (valueAt s 4 * valueAt s 6 = valueAt s 2)).toNat

/-- The result. -/
def stBit (s : State) : BitVec 32 := (prBit s &&& pcBit s) &&& 1

/-- `x = R² mod n` read from `pre`, after the public precompute wrote it. -/
theorem x_of_pc {s : State} (A : PPABI s) {m : Mem} {ws : List (BitVec 64)} (hp : Spec.Rsa.publicPrecompute (nBytes s) = some ws)
    (hw : Spec.Rsa.wordsAt m (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) = ws) :
    xPre s m = 2 ^ (128 * Spec.Rsa.modulusWords (arg s 3).toNat) % Spec.Rsa.os2ip (nBytes s) := by
  have hlen : (nBytes s).length = (arg s 3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  let N := Spec.Rsa.os2ip (nBytes s)
  let w := Spec.Rsa.modulusWords (arg s 3).toNat
  have hNl : N < 2 ^ (8 * (arg s 3).toNat) := by
    have := VG.Proof.Bignum.os2ip_lt (nBytes s)
    rwa [hlen, VG.Proof.Bignum.pow256_eq] at this
  have hw8 : (arg s 3).toNat ≤ 8 * w := by simp only [w, Spec.Rsa.modulusWords]; omega_using []
  have hNw : N < 2 ^ (64 * w) := Nat.lt_of_lt_of_le hNl (Nat.pow_le_pow_right (by decide) (by omega_using [hw8]))
  unfold Spec.Rsa.publicPrecompute at hp
  rw [hlen] at hp
  simp only at hp
  by_cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s)) (arg s 3).toNat = true
  · simp only [hv, ite_true, Option.some.injEq] at hp
    subst hp
    have hpos : 0 < N := by
      have hv' := hv
      rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv'
      obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := hv'
      have := beq_iff_eq.mp h1
      show 0 < Spec.Rsa.os2ip (nBytes s)
      omega_using [this]
    have hR : 2 ^ (128 * w) % N < 2 ^ (64 * w) := Nat.lt_trans (Nat.mod_lt _ hpos) hNw
    obtain ⟨-, hwv⟩ := VG.Proof.Bignum.pre_words hw hNw hR
    have rd := VG.Proof.Bignum.read_eq_wv m (argumentPointer s 0) (8 * w) w
    rw [hwv] at rd
    have sp := VG.Proof.Mont.read_toNat_add m (8 * w - (arg s 3).toNat) (arg s 3).toNat
      (off (argumentPointer s 0) (8 * w))
    rw [show 8 * w - (arg s 3).toNat + (arg s 3).toNat = 8 * w by omega_using [hw8], rd] at sp
    have hx : xPre s m = (m.read (off (argumentPointer s 0) (8 * w)) (arg s 3).toNat).toNat := by
      show (m.read ((inV s).setWidth 64) (arg s 3).toNat).toNat = _
      rw [inV_ptr A]
    rw [hx]
    have hRl : 2 ^ (128 * w) % N < 2 ^ (8 * (arg s 3).toNat) := Nat.lt_trans (Nat.mod_lt _ hpos) hNl
    have hX : (m.read (off (argumentPointer s 0) (8 * w)) (arg s 3).toNat).toNat < 2 ^ (8 * (arg s 3).toNat) :=
      BitVec.isLt _
    rw [← Nat.mod_eq_of_lt hX, ← Nat.add_mul_mod_self_left _ (2 ^ (8 * (arg s 3).toNat)), ← sp,
      Nat.mod_eq_of_lt hRl]
  · simp [hv] at hp

/-- `pre`'s values before the mask, for `x` what `primes` read. -/
structure PreVals (s : State) (X : Nat) (m : Mem) : Prop where
  pub : Spec.Rsa.wordsAt m (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
    match Spec.Rsa.publicPrecompute (nBytes s) with
    | some ws => ws
    | none => List.replicate (2 * Spec.Rsa.modulusWords (arg s 3).toNat) 0
  p : X % CrtRt.safeM (valueAt s 4) = 2 ^ fixB (arg s 3).toNat % CrtRt.safeM (valueAt s 4) →
    val32 m (argumentPointer s 0) (dstOff s none) (2 * Spec.Rsa.primeWords (arg s 5).toNat) =
      2 ^ r2Exp (arg s 5).toNat % CrtRt.safeM (valueAt s 4)
  q : X % CrtRt.safeM (valueAt s 6) = 2 ^ fixB (arg s 3).toNat % CrtRt.safeM (valueAt s 6) →
    val32 m (argumentPointer s 0) (dstOff s (some 5)) (2 * Spec.Rsa.primeWords (arg s 7).toNat) =
      2 ^ r2Exp (arg s 7).toNat % CrtRt.safeM (valueAt s 6)
  x : ∀ ws, Spec.Rsa.publicPrecompute (nBytes s) = some ws →
    X = 2 ^ (128 * Spec.Rsa.modulusWords (arg s 3).toNat) % Spec.Rsa.os2ip (nBytes s)

section
variable {s : State}

theorem val32_frame {rs : List Region} {m m' : Mem} (F : Frame rs m m') {base : Addr} {d n : Nat}
    (hd : ∀ r ∈ rs, (⟨off base d, 4 * n⟩ : Region).Disjoint r) (hn : 4 * n < 2 ^ 64) :
    val32 m' base d n = val32 m base d n := by
  rw [← read_eq_val32, ← read_eq_val32, F.read (r := ⟨off base d, 4 * n⟩) (Region.contains_self _ _) hd hn]

/-- A word of the frame, kept by writes to the frame's other words. -/
theorem slot_frame {rs : List Region} {m m' : Mem} (F : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨slot s d, 4⟩ : Region).Disjoint r) : m'.readW (slot s d) 32 = m.readW (slot s d) 32 :=
  F.readW (Region.contains_self _ _) hd (by decide)

theorem body_ok {pcName prName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (prst : stackUse primes ≤ 96) (prns : NoSp primes) (A : PPABI s) :
    WP isa (body pcName pc prName primes) (allocFrame Impl.Bignum.X86.PrivPre.frameBytes s) fun v =>
      Body s v ∧ Keeps [.eax, .ecx, .edx] (allocFrame Impl.Bignum.X86.PrivPre.frameBytes s) v ∧
      v.gpr .eax = stBit s ∧ ∃ X m, PreVals s X m ∧ ∀ i < (arg s 1).toNat * 8,
        v.mem (argumentPointer s 0 + BitVec.ofNat 64 i) =
          m (argumentPointer s 0 + BitVec.ofNat 64 i) &&& (0 - stBit s).setWidth 8 := by
  have parts := pre_parts A
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  have pw5 : Spec.Rsa.primeWords (arg s 5).toNat ≤ Spec.Rsa.modulusWords (arg s 3).toNat := by
    have := A.pLength; simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_using [l, this]
  have pw7 : Spec.Rsa.primeWords (arg s 7).toNat ≤ Spec.Rsa.modulusWords (arg s 3).toNat := by
    have := A.qLength; simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_using [l, this]
  have hW : 16 * Spec.Rsa.modulusWords (arg s 3).toNat = dstOff s none := rfl
  -- the regions the frame's words and `pre`'s parts are in
  have topSub : ∀ {d n : Nat}, d + n ≤ 196 → Region.Sub ⟨bot s + BitVec.ofNat 64 d, n⟩ (topR s) :=
    fun h => Offset.sub_base _ (by simpa [stackBytes] using h)
  let rest : Region := ⟨off (argumentPointer s 0) (dstOff s none),
    8 * Spec.Rsa.primeWords (arg s 5).toNat + 8 * Spec.Rsa.primeWords (arg s 7).toNat⟩
  have restSub : Region.Sub rest (preR s) := Offset.sub_base _ (by simp only [dstOff] at parts ⊢; omega_using [parts])
  have s80 : ∀ {r : Region}, (topR s).Disjoint r → (⟨slot s statusOffset, 4⟩ : Region).Disjoint r :=
    fun h => h.sub_left (topSub (d := 100 + statusOffset) (by decide))
  unfold body
  refine WP.seq (WP.mono (publicArgs_ok A Body.start) fun u₁ ⟨B₁, K₁, F₁, V₁⟩ => ?_)
  refine WP.seq (WP.mono (pc_call pv pst pns A B₁ V₁) fun u₂ ⟨B₂, K₂, F₂, O₂⟩ => ?_)
  refine WP.seq (WP.mono (primesArgs_ok A B₂) fun u₃ ⟨B₃, K₃, F₃, S₃, V₃⟩ => ?_)
  refine WP.seq (WP.mono (pr_call prst prns A B₃ V₃) fun u₄ ⟨B₄, K₄, F₄, O₄⟩ => ?_)
  refine WP.seq (WP.mono (status_ok A B₄) fun u₅ ⟨B₅, K₅, F₅, S₅⟩ => ?_)
  refine WP.seq (WP.mono (copyPrimes_ok A B₅) fun u₆ ⟨B₆, K₆, F₆, P₆, Q₆⟩ => ?_)
  refine WP.seq (WP.mono (maskArgs_ok A B₆) fun u₇ ⟨B₇, K₇, F₇, S₇, D₇, C₇⟩ => ?_)
  refine WP.seq (WP.mono (maskLoop_ok A B₇ D₇ C₇) fun u₈ ⟨B₈, K₈, F₈, M₈⟩ => ?_)
  refine wp_movS (B₈.readSlot A (d := statusOffset) (by decide)) fun u₉ a₉ _ => WP.block_nil ?_
  -- the status word
  have e₂ : u₂.gpr .eax = pcBit s := by
    unfold PcOut at O₂; unfold pcBit
    cases h : Spec.Rsa.publicPrecompute (nBytes s) <;> simp only [nBytes] at h <;> simp only [h] at O₂ ⊢ <;>
      exact O₂.1
  have st4 : u₄.mem.readW (slot s statusOffset) 32 = pcBit s := by
    rw [slot_frame F₄ fun r hr => ?_, show slot s statusOffset = slot s 80 from rfl, S₃, e₂]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact s80 A.belowWs
    · exact Offset.disjoint_base _ (by decide) (by decide)
  have st5 : u₅.mem.readW (slot s statusOffset) 32 = stBit s := by
    rw [S₅, st4, O₄.1]; rfl
  have st6 : u₆.mem.readW (slot s statusOffset) 32 = stBit s := by
    rw [slot_frame F₆ fun r hr => ?_, st5]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact s80 (A.belowPre.sub_right restSub)
  have st7 : u₇.mem.readW (slot s statusOffset) 32 = stBit s := by
    rw [slot_frame F₇ fun r hr => ?_, st6]
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have mk : mask8 s u₇.mem = (0 - stBit s).setWidth 8 := by
    simp only [mask8]; rw [S₇, st6]
  refine ⟨B₈.next (a₉.other _ (by decide)) a₉.rd a₉.wr (by rw [a₉.mem]; exact Frame.refl _ _), ?_, ?_,
    xPre s u₃.mem, u₇.mem, ?_, fun i hi => by rw [a₉.mem, M₈ i hi, mk]⟩
  · exact ((((((((K₁.mono (by simp)).trans (K₂.mono (by simp))).trans (K₃.mono (by simp))).trans
      (K₄.mono (by simp))).trans (K₅.mono (by simp))).trans (K₆.mono (by simp))).trans (K₇.mono (by simp))).trans
      (K₈.mono (by simp))).trans (a₉.keeps.mono (by simp))
  · rw [a₉.gpr, slot_keep A (F₈.mono fun r hr => by simp at hr; simp [hr]) (by decide), st7]
  · have preSub : ∀ {d n : Nat}, d + n ≤ (arg s 1).toNat * 8 →
        Region.Sub ⟨off (argumentPointer s 0) d, n⟩ (preR s) := fun h => Offset.sub_base _ h
    have preTop : ∀ {d n e k : Nat}, d + n ≤ (arg s 1).toNat * 8 → e + k ≤ 196 →
        (⟨off (argumentPointer s 0) d, n⟩ : Region).Disjoint ⟨bot s + BitVec.ofNat 64 e, k⟩ :=
      fun h h' => ((A.belowPre.sub_left (topSub h')).sub_right (preSub h)).symm
    have F₂₇ : Frame [topR s, wsR s, rest] u₂.mem u₇.mem := by
      refine (((F₃.sub ?_).trans (F₄.sub ?_)).trans (F₅.sub ?_)).trans ((F₆.sub ?_).trans (F₇.sub ?_)) <;>
        intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      · subst hr; exact ⟨topR s, by simp, topSub (d := 100 + 0) (by decide)⟩
      · rcases hr with rfl | rfl
        · exact ⟨wsR s, by simp, fun _ h => h⟩
        · exact ⟨topR s, by simp, Region.sub_prefix (by simp [stackBytes])⟩
      · subst hr; exact ⟨topR s, by simp, topSub (d := 100 + statusOffset) (by decide)⟩
      · rcases hr with rfl | rfl
        · exact ⟨topR s, by simp, topSub (d := 100 + 88) (by decide)⟩
        · exact ⟨rest, by simp [rest], fun _ h => h⟩
      · subst hr; exact ⟨topR s, by simp, topSub (d := 100 + (statusOffset + 4)) (by decide)⟩
    have W : Spec.Rsa.wordsAt u₇.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
        Spec.Rsa.wordsAt u₂.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) := by
      refine VG.Proof.Rsa.wordsAt_frame F₂₇ (by simp only [dstOff] at parts; omega_using [parts]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact A.belowPre.symm.sub_left (Region.sub_prefix (by simp only [dstOff] at parts; omega_using [parts]))
      · exact A.preWs.sub_left (Region.sub_prefix (by simp only [dstOff] at parts; omega_using [parts]))
      · exact Offset.base_disjoint _ (by simp only [dstOff]; omega_using []) (by simp only [dstOff] at parts ⊢; omega_using [parts])
    have W₃ : Spec.Rsa.wordsAt u₃.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
        Spec.Rsa.wordsAt u₂.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) := by
      refine VG.Proof.Rsa.wordsAt_frame F₃ (by simp only [dstOff] at parts; omega_using [parts]) fun r hr => ?_
      obtain rfl := List.mem_singleton.mp hr
      exact A.belowPre.symm.sub_left (Region.sub_prefix (by simp only [dstOff] at parts; omega_using [parts])) |>.sub_right
        (topSub (d := 100 + 0) (by decide))
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold PcOut at O₂
      cases h : Spec.Rsa.publicPrecompute (nBytes s) <;> simp only [nBytes] at h <;> simp only [h] at O₂ ⊢ <;>
        rw [W] <;> exact O₂.2
    · intro hX
      rw [val32_frame F₇ (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact preTop (by simp only [dstOff] at parts ⊢; omega_using [parts]) (by decide))
          (by simp only [Spec.Rsa.modulusWords] at pw5; omega_using [pw5]), P₆,
        ws_keep F₅ (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (s80 A.belowWs).symm)
          (slot_fit A (by decide) pw5)]
      exact O₄.2.1 hX
    · intro hX
      rw [val32_frame F₇ (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact preTop (by omega_using [parts]) (by decide)) (by simp only [Spec.Rsa.modulusWords] at pw7; omega_using [parts]), Q₆,
        ws_keep F₅ (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (s80 A.belowWs).symm)
          (slot_fit A (by decide) pw7)]
      exact O₄.2.2 hX
    · intro ws hp
      unfold PcOut at O₂
      simp only [nBytes] at hp
      simp only [hp] at O₂
      exact x_of_pc A hp (W₃.trans O₂.2)

end
end VG.Proof.Bignum.X86.PrivPre
