module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.CrtSave

/-! # Functional correctness of `vg_rsa_private_crt_precomputed` on x86

What `privateCrtPrecomputedContract` gives at the entry: each factor's
cached `R² mod p` in `pre` (`preR2_of`, from its words, `val32_of_wordsAt`)
and apart from the output (`preOut_of`); `bodyP_ok`: the modulus checked,
then `sizedPre_ok` or the failure; `operationP_ok` and `correctP`, as
`operation_ok` and `correct` are of `vg_rsa_private_crt`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue specResult specResult_eq)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.CrtRt (preArg)

theorem wordsAt_append' (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- The number of `2 w` words of 32 bits at `p + d` whose `w` words of 64 bits are `toWords V w`. -/
theorem val32_of_wordsAt {m : Mem} {p : Addr} {d w V : Nat}
    (h : Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 d) w = Spec.Rsa.toWords V w) (hV : V < 2 ^ (64 * w)) :
    val32 m p d (2 * w) = V := by
  rw [← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega_using [], VG.Proof.Bignum.read_eq_wv,
    ← Nat.mod_eq_of_lt hV]
  refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
  have := congrArg (fun l => l[i]?) h
  simp only [Spec.Rsa.wordsAt, Spec.Rsa.toWords, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  show (m.readW (off p (d + 8 * i)) 64).toNat = _
  rw [show off p (d + 8 * i) = p + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * i) by
    rw [Offset.add_add], this, BitVec.toNat_ofNat]

theorem toWords_length' (x w : Nat) : (Spec.Rsa.toWords x w).length = w := by
  simp only [Spec.Rsa.toWords, List.length_map, List.length_range]

theorem wordsAt_length' (m : Mem) (p : Addr) (w : Nat) : (Spec.Rsa.wordsAt m p w).length = w := by
  simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range]

section
variable {s : State}

/-- The first `n` bytes of `pre`. -/
theorem pre_sub (n k : Nat) (h : n ≤ k) (P : Addr) :
    Region.Sub ⟨P, n⟩ ⟨P, k⟩ := by
  have := Offset.sub P (d := 0) (n := n) (e := 0) (k := k) (Nat.zero_le _) (by omega_using [h])
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- Factor `i`'s cached value, from the contract's `pre`, for a factor above one. -/
theorem preR2_of (A : CrtABIP s) {i : Nat} (hi : i ≤ 1)
    (hp : 1 < componentValue s.mem (arg s) (6 + 2 * i)) :
    PreR2 s (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i
      (componentValue s.mem (arg s) (6 + 2 * i)) := by
  have lv := A.lengths
  have pl := A.pLength
  have ql := A.qLength
  have pp := A.pPositive
  have qp := A.qPositive
  have plen := A.preLength
  have pb := A.preBound
  unfold Spec.Rsa.lenValid at lv
  have pwq : preOff (arg s) i + 8 * preW (arg s) i ≤ (arg s 19).toNat * 8 := by
    rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> simp [preOff, preW] <;> omega_using [plen]
  have below' : Region.Disjoint (below (s.gpr .esp) 96) ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth A.stackLow]; exact A.belowPre
  have sub := pre_sub _ _ pwq (argumentPointer s 18)
  refine ⟨⟨VG.Proof.Dsa.X86.stackArgument_of (count := 20) (by have := A.stackBound; omega_using [this]) (by decide)
      (by rw [A.rd, A.wr]; simp) A.scratchArgs.symm, rfl⟩, hi, ?_, ?_, by omega_using [lv, pl], by omega_using [pp],
    ⟨⟨argumentPointer s 18, (arg s 19).toNat * 8⟩, by rw [A.rd]; simp, ?_⟩, by simp only [preArg]; omega_using [pb, pwq],
    A.scratchPre.symm.sub_left sub, ?_,
    by have := A.stackBound; omega_using [this], below'.symm.sub_left sub⟩
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd] <;> omega_arith
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd] <;> omega_arith
  · have := Offset.contains_base (argumentPointer s 18) (d := 0) (n := preOff (arg s) i + 8 * preW (arg s) i)
      (k := (arg s 19).toNat * 8) (by omega_using [pwq]) (by decide)
    simp only [BitVec.add_zero] at this
    exact this
  · have W := A.preValue
    rw [plen, wordsAt_append'] at W
    obtain ⟨E1, E2⟩ := List.append_inj W (by
      rw [wordsAt_length', Spec.Rsa.primeR2, toWords_length', VG.Proof.Bignum.bytesAt_length])
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length] at E1 E2
    have lt : ∀ j, componentValue s.mem (arg s) j < 2 ^ (64 * Spec.Rsa.primeWords (arg s (j + 1)).toNat) := by
      intro j
      refine Nat.lt_of_lt_of_le (comp_lt s.mem (arg s) j) (Nat.pow_le_pow_right (by decide) ?_)
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_using []
    rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
    · have E1' : Spec.Rsa.wordsAt s.mem (argumentPointer s 18 + BitVec.ofNat 64 0)
          (Spec.Rsa.primeWords (arg s 7).toNat) = Spec.Rsa.toWords
            (2 ^ (128 * Spec.Rsa.primeWords (arg s 7).toNat) % componentValue s.mem (arg s) 6)
            (Spec.Rsa.primeWords (arg s 7).toNat) := by
        rw [show argumentPointer s 18 + BitVec.ofNat 64 0 = argumentPointer s 18 from BitVec.add_zero _]
        exact E1
      exact val32_of_wordsAt (p := argumentPointer s 18) (d := 0) E1' (Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) (lt 6))
    · exact val32_of_wordsAt (p := argumentPointer s 18) (d := 8 * Spec.Rsa.primeWords (arg s 7).toNat) E2
        (Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) (lt 8))

/-- Argument 18 and factor `i`'s cached value, apart from the output. -/
theorem preOut_of (A : CrtABIP s) {i : Nat} (hi : i ≤ 1) : PreOut s (arg s) (arg s 3).toNat i := by
  have plen := A.preLength
  have pwq : preOff (arg s) i + 8 * preW (arg s) i ≤ (arg s 19).toNat * 8 := by
    rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> simp [preOff, preW] <;> omega_using [plen]
  have pb := A.preBound
  have ol := A.outLength
  have O : VG.Proof.Dsa.X86.StackArgument s (argumentPointer s 0) (arg s 1).toNat preArg :=
    VG.Proof.Dsa.X86.stackArgument_of (count := 20) (by have := A.stackBound; omega_using [this]) (by decide) (by rw [A.rd, A.wr]; simp)
      A.outArgs.symm
  refine ⟨?_, ?_⟩
  · rw [← ol]; exact O.apart
  · rw [← ol]; exact A.outPre.symm.sub_left (pre_sub _ _ pwq _)

end

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- With `pre`: what `sized_post` states. -/
theorem sizedP_post (h : RIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true)
    (pq : componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2)
    (P0 : 1 < componentValue s.mem args 6 → PreR2 s base bytes len args 0 (componentValue s.mem args 6))
    (O0 : PreOut s args len 0)
    (P1 : 1 < componentValue s.mem args 8 → PreR2 s base bytes len args 1 (componentValue s.mem args 8))
    (O1 : PreOut s args len 1) :
    WP isa (CrtRt.sized true) s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain ⟨odd, pN, qN⟩ := h.crt.factor_bounds valid
  obtain ⟨q1, qo⟩ := VG.Proof.Bignum.factor_facts pq pN odd
  obtain ⟨p1, po⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact pq) qN odd
  have sp := safeM_of p1 po
  have sq := safeM_of q1 qo
  refine WP.mono (sizedPre_ok h valid pq (by rw [sp]; exact P0 p1) O0 (by rw [sq]; exact P1 q1) O1)
    fun t ⟨Y, B, F, K⟩ => ⟨⟨?_, F⟩, K⟩
  rw [specResult_eq, h.crt.modulus_length, valid]
  by_cases acc : accepted s.mem args
  · simp only [ite_true, acc, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_true]; rfl, by simpa only [acc, ite_true] using Y⟩
  · simp only [ite_true, acc, ite_false, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_false]; rfl,
      by simpa only [acc, ite_false, VG.Proof.Bignum.i2osp_zero'] using Y⟩

/-- With `pre`: the modulus checked, then `sizedPre_ok` or the failure. -/
theorem bodyP_ok (h : RIn base bytes len args s)
    (pq : componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2)
    (P0 : 1 < componentValue s.mem args 6 → PreR2 s base bytes len args 0 (componentValue s.mem args 6))
    (O0 : PreOut s args len 0)
    (P1 : 1 < componentValue s.mem args 8 → PreR2 s base bytes len args 1 (componentValue s.mem args 8))
    (O1 : PreOut s args len 1) :
    WP isa (CrtRt.body true) s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nf := h.crt.fits 2 (by decide)
  have nr := h.crt.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [h.crt.modulus_length] at nf nr
  unfold CrtRt.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.crt.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower' h.upper' (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  have modulus : componentValue s.mem args 2 =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) := by
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat) = _
    rw [h.crt.modulus_length]
  rw [← modulus] at Z
  have Fv : Frame [] s.mem v.mem := by rw [Msv]; exact Frame.refl _ _
  have keepP : ∀ {i p : Nat}, PreR2 s base bytes len args i p → PreR2 v base bytes len args i p :=
    fun P => P.keep Ksv (by decide) Fv (fun _ h => nomatch h) (fun _ h => nomatch h)
  refine WP.ite (Spec.Rsa.modulusValid (componentValue s.mem args 2) len) Z ?_ ?_
  · intro valid
    refine WP.mono (sizedP_post hv (by rw [Msv]; exact valid) (by rw [Msv]; exact pq)
      (by rw [Msv]; exact fun g => keepP (P0 g)) (O0.keep Ksv (by decide))
      (by rw [Msv]; exact fun g => keepP (P1 g)) (O1.keep Ksv (by decide))) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩
  · intro invalid
    have failed : specResult v.mem args = none := by
      rw [specResult_eq, Msv, h.crt.modulus_length, invalid]
      rfl
    refine WP.mono (failure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩

end

open VG.Proof.Dsa.X86 (argumentPointer) in
theorem operationP_ok {s : State} (A : CrtABIP s) :
    WP isa (CrtRt.code true) s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (specResult s.mem (arg s)) ∧ abiPreserved s t := by
  have R := A.res
  have low : 48 ≤ (arg s 17).toNat * 8 := by have := R.used; omega_using [this]
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega_using []
  unfold CrtRt.code
  rw [entry_eq]
  refine WP.seq (WP.mono (Crt.installedG_ok R) fun u ⟨I, S, K, O⟩ => ?_)
  have hI : RIn (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u :=
    In.ofInputs I (need_le A.lengths.1 A.scratchLength)
      (by simp only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))]) rfl
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega_using [])
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have C (i : Nat) (hi : i ∈ componentArguments) : componentValue u.mem (arg s) i = componentValue s.mem (arg s) i := by
    unfold componentValue; rw [B i hi]
  -- `pre`'s values, through the entry, which changes only the working space.
  have Fe : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩] s.mem u.mem := by
    have F := VG.Proof.Bignum.outside_frame O (by omega_using [])
    simpa only [off, BitVec.add_zero] using F
  have keepP : ∀ {i p : Nat}, PreR2 s (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i p →
      PreR2 u (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i p := fun P =>
    P.keep K (by decide) Fe (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).1)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).2)
  have pq : componentValue u.mem (arg s) 6 * componentValue u.mem (arg s) 8 = componentValue u.mem (arg s) 2 := by
    rw [C 6 (by decide), C 8 (by decide), C 2 (by decide)]; exact A.product
  refine WP.seq (WP.mono (bodyP_ok hI pq
    (fun g => by rw [C 6 (by decide)] at g ⊢; exact keepP (preR2_of A (i := 0) (by decide) g))
    ((preOut_of A (i := 0) (by decide)).keep K (by decide))
    (fun g => by rw [C 8 (by decide)] at g ⊢; exact keepP (preR2_of A (i := 1) (by decide) g))
    ((preOut_of A (i := 1) (by decide)).keep K (by decide))) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have Saved := frameRt_saved F I.outApart low high I.room.apart (savedRegisters_eq ▸ S)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  rw [espu] at F
  have Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    have Start := VG.Proof.Bignum.outside_frame O (by omega_using [])
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (frameRt_full F low)
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact A.retScratch
    · rw [← A.outLength]; exact A.retOut
    · exact ret_zone40 A.stackLow
  rw [restore_eq]
  refine WP.mono (Crt.entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low
    (savedRegisters_eq ▸ Saved)) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have Specs : specResult u.mem (arg s) = specResult s.mem (arg s) := by
    unfold specResult
    rw [B 2 (by decide), B 4 (by decide), B 6 (by decide), B 8 (by decide),
      B 10 (by decide), B 12 (by decide), B 14 (by decide)]
  rw [Specs] at V
  exact V

theorem correctP (s : State) (h : (privateCrtPrecomputedContract abi 96).pre s) :
    ∃ trace t, Exec isa (CrtRt.code true) s trace t ∧ abiPreserved s t ∧
      (privateCrtPrecomputedContract abi 96).post s t := by
  have A := crtABIP_of h
  obtain ⟨trace, t, E, V, P⟩ := operationP_ok A
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
    argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold specResult at V
  rw [A.inLength, A.dpLength, A.dqLength, A.qiLength] at V
  exact V

end VG.Proof.Bignum.X86.CrtRt
