module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Main
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em

/-!
# RSAES-OAEP encryption on PPC64LE: the public-key operation, and failing

Untrusted: everything here is checked by Lean. `pubArgs_ok`: the arguments
of `vg_rsa_public_precomputed_checked` (`AtCall`): `out`, `pre`, `e`, `EM`
at `S` and the rest of the working space; `call_ok`: the call writes RSAEP
of `EM` to `out` if `pre` holds the modulus' values (`AfterCall`), by its
contract (`Proof/RsaPkcs1Sig/PPC64LE/Callee.lean`); `fail_ok`: `encFail`
writes zeros to `out` and returns 0.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_std wp_addSp wp_nil PdOk
  PdLay pdRd pdWr pdCall)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (S s) oRsa, ((stackArg s 4).toNat - 1024) * 8⟩

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`, with `EM` the encoding at `S`. -/
structure AtCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  mem : Frame [kR s, SC s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM
  g3 : t.gpr .r3 = s.gpr .r3
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 5
  g6 : t.gpr .r6 = stackArg s 6
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = off (S s) 0
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = off (S s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 4).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem scl : 1024 ≤ (stackArg s 4).toNat := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega

theorem rsa_sub : Region.Sub (rsaR s) (scR s) := by
  have := scl P
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem pubArgs_ok {t : State} {EM : List Byte} (h : Base s t) (he : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM) :
    WP isa (.block pubArgs) t (AtCall s EM) := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hsc := scl P
  have hk2 : kk s ≤ 1024 := P.k2
  simp only [pubArgs]
  refine wp_addSp fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ => ?_
  rw [h.sp, BitVec.add_zero] at e₁
  have g12₃ : t₃.gpr .r12 = fb s := by rw [o₃.get .r12, o₂.get .r12, e₁]
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [g12₃])
    (by rw [o₃.wr, o₂.wr, o₁.wr, h.wr]; exact in_fr s _ (by decide) (by decide)) fun t₄ m₄ => ?_
  refine wp_subi (h := by decide) fun t₅ o₅ e₅ => ?_
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₅.get .r12, m₄.gpr, g12₃])
    (by rw [o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, h.wr]; exact in_fr s _ (by decide) (by decide)) fun t₆ m₆ => ?_
  refine wp_mov fun t₇ o₇ e₇ => wp_mov fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ =>
    wp_mov fun t₁₁ o₁₁ e₁₁ => wp_mov fun t₁₂ o₁₂ e₁₂ => wp_addi fun t₁₃ o₁₃ e₁₃ => wp_mov fun t₁₄ o₁₄ e₁₄ =>
    wp_nil ?_
  have k₃ : Only [.r12, .r4, .r4] t t₃ := o₁.trans (o₂.trans o₃)
  have k₁₄ : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] t₆ t₁₄ :=
    (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))))))).mono
  -- The two stack arguments.
  have fr₆ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t₃.mem t₆.mem := by
    rw [m₆.mem, o₅.mem, m₄.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  have hK : Keep [.r12, .r4, .r5, .r3, .r6, .r7, .r8, .r9, .r10] t t₁₄ :=
    (k₃.keep.trans (m₄.keep.trans (o₅.keep.trans (m₆.keep.trans k₁₄.keep)))).mono
  have hfr : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t.mem t₁₄.mem := by
    rw [k₁₄.mem, ← k₃.mem] at *; exact fr₆
  have hds : (slR s).Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have sv : Saves s t₁₄ := h.sv.keep hK hfr (fun r hr => by rw [List.mem_singleton.mp hr]; exact hds)
  have hsp : t₁₄.sp = fb s := sv.sp
  refine ⟨sv, hK.rd.trans h.rd, h.mem.trans (hfr.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨kR s, by simp, frame_sub s (by decide)⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← he]
    exact bytes_entry (A := ⟨fb s + BitVec.ofNat 64 96, 16⟩) (B := ⟨fb s + BitVec.ofNat 64 96, 16⟩)
      (hfr.mono fun r hr => by simp at hr ⊢; exact hr)
      ((k_sc P).sub_left (frame_sub s (by decide)) |>.sub_right (sc_in (by omega)))
      ((k_sc P).sub_left (frame_sub s (by decide)) |>.sub_right (sc_in (by omega))) (by omega)
  · rw [o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, o₉.get .r3, o₈.get .r3, e₇, m₆.gpr,
      o₅.get .r16, m₄.gpr, k₃.get .r16, h.r16]
  · rw [o₁₄.get .r4, o₁₃.get .r4, o₁₂.get .r4, o₁₁.get .r4, o₁₀.get .r4, o₉.get .r4, e₈, o₇.get .r15, m₆.gpr,
      o₅.get .r15, m₄.gpr, k₃.get .r15, h.r15]
  · rw [o₁₄.get .r5, o₁₃.get .r5, o₁₂.get .r5, o₁₁.get .r5, o₁₀.get .r5, e₉, o₈.get .r21, o₇.get .r21, m₆.gpr,
      o₅.get .r21, m₄.gpr, k₃.get .r21, h.r21]
  · rw [o₁₄.get .r6, o₁₃.get .r6, o₁₂.get .r6, o₁₁.get .r6, e₁₀, o₉.get .r22, o₈.get .r22, o₇.get .r22, m₆.gpr,
      o₅.get .r22, m₄.gpr, k₃.get .r22, h.r22]
  · rw [o₁₄.get .r7, o₁₃.get .r7, o₁₂.get .r7, e₁₁, o₁₀.get .r17, o₉.get .r17, o₈.get .r17, o₇.get .r17, m₆.gpr,
      o₅.get .r17, m₄.gpr, k₃.get .r17, h.r17]
  · rw [o₁₄.get .r8, o₁₃.get .r8, e₁₂, o₁₁.get .r18, o₁₀.get .r18, o₉.get .r18, o₈.get .r18, o₇.get .r18, m₆.gpr,
      o₅.get .r18, m₄.gpr, k₃.get .r18, h.r18]
  · rw [o₁₄.get .r9, e₁₃, o₁₂.get .r14, o₁₁.get .r14, o₁₀.get .r14, o₉.get .r14, o₈.get .r14, o₇.get .r14,
      m₆.gpr, o₅.get .r14, m₄.gpr, k₃.get .r14, h.r14, hE]
  · rw [e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15, o₇.get .r15,
      m₆.gpr, o₅.get .r15, m₄.gpr, k₃.get .r15, h.r15]
  · show t₁₄.mem.readW (stackArgAddr t₁₄ 0) 64 = _
    rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide)
      (by decide)) (by decide), o₅.mem, m₄.mem, Mem.readW_writeW_self64, e₃, o₂.get .r14, o₁.get .r14, h.r14, e₂]
  · show t₁₄.mem.readW (stackArgAddr t₁₄ 1) 64 = _
    rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_self64, e₅, m₄.gpr, k₃.get .r23, h.r23,
      sub_k (by omega)]

theorem oR_eq : oR s = ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [oR, P.ok]

theorem pdOk_of {t : State} {EM : List Byte} (ha : AtCall s EM t) : PdOk t := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk1 := P.k1; have hk2 := P.k2
  have hsc := scl P
  have hsp : t.sp = fb s := ha.sv.sp
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, hsp]
  have hS := S_fits P
  have hwsc := P.wsc
  have eS : (S s).toNat = (stackArg s 3).toNat := rfl
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hem : Region.Sub ⟨off (S s) 0, (s.gpr .r6).toNat⟩ (scR s) :=
    fun x hx => sc_sub P x (sc_in (by unfold oRsa; omega) x hx)
  have hfa : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (by decide)
  have h1 : (stackArg t 1).toNat = (stackArg s 4).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, h1, hsa]
    exact {
      on := by rw [← oR_eq P]; exact P.op
      oe := by rw [← oR_eq P]; exact P.oe
      oi := by rw [← oR_eq P]; exact P.osc.sub_right hem
      os := by rw [← oR_eq P]; exact P.osc.sub_right (rsa_sub P)
      oa := (hko.sub_left hfa).symm
      ns := P.sp.symm.sub_right (rsa_sub P)
      es := P.es.sub_right (rsa_sub P)
      is := Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      sa := ((P.ksc.sub_left hfa).sub_right (rsa_sub P)).symm
      wo := by have := P.wo; rw [P.ok] at this; exact this
      wn := P.wp
      we := P.we
      wi := by
        show (S s + BitVec.ofNat 64 0).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.add_zero]; unfold oRsa at hS; omega
      ws := by
        show (S s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 4).toNat - 1024) * 8 ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega }
  case sp =>
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes]; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.sv.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [P.hrd]; simp)) (Covers.cons (hm _ (by rw [P.hrd]; simp))
      (Covers.cons (Covers.right (sc_cov P (by unfold oRsa; omega)))
        (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, h1, ha.sv.wr]
    refine Covers.cons (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [P.hwr, oR_eq P]; simp))
      (Covers.cons ?_ Covers.nil)
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨scR s, by rw [P.hwr]; simp, oRsa, rfl, by simp only; unfold oRsa; omega⟩
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact P.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact P.e1
  case he2 => rw [ha.g8, ha.g4]; exact P.e2
  case hs =>
    rw [ha.g4, h1]; have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega

/-- After the call: what the restores need, and `out` written with RSAEP of
`EM` if `pre` holds the modulus' values. -/
structure AfterCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) EM)

theorem call_ok {t : State} {EM : List Byte} (ha : AtCall s EM t) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.pubCall t (AfterCall s EM) := by
  have hk2 := P.k2
  refine pdCall (pdOk_of P ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 4).isLt; omega)] at hf
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hd : ∀ r ∈ [(⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region), rsaR s], (slR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (slR_sub s)
    · exact (P.ksc.sub_left (slR_sub s)).sub_right (rsa_sub P)
  refine ⟨⟨hsp'.trans ha.sv.sp, hwr'.trans ha.sv.wr, fun r hr => (hpres r (by revert r; decide)).trans (ha.sv.hi r hr),
    ha.sv.sv.frame hf fun p hp' r hr => (hd r hr).sub_left (by
      have := saved_offs p hp'
      exact Offset.sub _ (n := 8) (by omega) (by unfold oLr at *; omega)),
    by
      rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
        (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
      exact ha.sv.ls⟩, fun hc => ?_⟩
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat := by
    rw [ha.g5, ha.g6]; exact words_entry ha.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, ha.em,
    bytes_entry ha.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega)] at this
  exact this

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
  have hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_))
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega) (by have := P.wo; omega)⟩
  refine WP.mono (zero_ok (p := s.gpr .r3) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r16]) (by rw [e₃ |> fun _ => o₃.get .r5, e₂, o₁.get .r15, h.r15]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hf : Frame [⟨s.gpr .r3, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  refine ⟨h.sv.keep ((k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.r3, .r4, .r5, .r6])) hf
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)), by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    (by simp; omega)
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaOaep.PPC64LE
