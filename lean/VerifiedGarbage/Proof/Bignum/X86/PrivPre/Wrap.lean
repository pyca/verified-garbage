module
-- separate module: the body's proof, apart from the arithmetic of its result

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.PrimesCall
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
