import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedMain
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {G : Spec.Mgf1.Hash}

theorem fail_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 3)) (R : Rep t.mem (fb s) (stackArg s 3) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hf : verifyOut G s = false) :
    WP isa verifyFail t (Done G s) :=
  WP.mono (vfail_done L R hw hcs h41 h42 h43 hf) fun _ D =>
    ⟨verifyOut G s, ⟨D.L, D.wr, D.cs, D.rbx, D.rbp, D.r12, D.out⟩, fun _ => rfl⟩

theorem restore_ok {s t : State} (d : Done G s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (validCache s → (verifyK G).post s (freedF t')) := by
  obtain ⟨b, D, hb⟩ := d
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · intro hc
    show (t'.gpr .rax).setWidth 32 = _
    rw [k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    change (t.gpr .rax).setWidth 32 = if verifyOut G s then 1 else 0
    rw [← hb hc]
    exact D.out

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem code_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) (v : PublicImpl)
    {s : State} (h : (Spec.RsaPss.verifyPrecomputedContract lk.G lk.G abi verifyStack).pre s) :
    WP isa (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (validCache s → (verifyK lk.G).post s s') := by
  have hp := pre_of lk.G h
  have hF := vfb_toNat hp.toVPre
  have hk1 := hp.k1; have hk2 := hp.k2
  refine wp_frame (by have := hp.sp1; unfold verifyStack frameBytes at *; omega) ?_
  rw [Impl.RsaPss.X86_64.Precomputed.body]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (verifyPro_ok hp.toVPre) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  have hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono (vn0_ok hp.toVPre L1 R1 (by simp [vproW, upd]) k1.2.1 hM1) fun t2 ⟨k2, hm2, hax2, hz2⟩ => ?_
  have L2 : Lay t2 (fb s) (stackArg s 3) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 3) _ (vproW s) := hm2 ▸ R1
  have hM2 : Frame (vwrR s) s.mem t2.mem := hm2 ▸ hM1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := Done lk.G s) ?_ fun t3 D => restore_ok D)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdi) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdi + 1) ((s.gpr .rsi).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega)
  have hrl : (n₀ :: rest).length = (s.gpr .rsi).toNat := by
    rw [← hnB]; simp [Spec.Rsa.bytesAt]
  have hout : verifyOut lk.G s = Spec.RsaPss.verify lk.G lk.G (n₀ :: rest)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)
      (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)) := by rw [verifyOut, hnB]
  have hfail : ∀ {t : State} {V : Nat → Byte} {W : Nat → BitVec 64}, Lay t (fb s) (stackArg s 3) →
      Rep t.mem (fb s) (stackArg s 3) V W → t.wr = frR s :: s.wr →
      (∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r) →
      W 41 = s.gpr .rbx → W 42 = s.gpr .rbp → W 43 = s.gpr .r12 → verifyOut lk.G s = false →
      WP isa verifyFail t (Done lk.G s) := fun L R hw hcs a b c d => fail_done L R hw hcs a b c d
  refine WP.ite (M := isa) _ (show isa.eval .e t2 = _ from hz2) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine hfail L2 R2 hw2 hcs2 (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) ?_
    rw [hout, h0]; exact RsaPss.verify_zero ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl : lk.G.len = H.D := lk.len
  have hEL := emLen_eq (rest := rest) h0
  rw [hrl] at hEL
  have hlo : loV n₀.toNat ≤ 1 := by unfold loV; split <;> omega
  -- `smear(n₀ >> 1)`.
  refine WP.seq (WP.mono (smear_ok t2 (x := n₀.toNat) n₀.isLt hb hax2) fun t3 ⟨k3, hm3, hdx3, hz3⟩ => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 3) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 3) _ (vproW s) := hm3 ▸ R2
  -- `emLen`, the mask and `lo`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [emLen]) (by exact Nat.zero_le 8)
    (emLen_ok (H := H) (by omega) L3 R3 (x := n₀.toNat) (k := (s.gpr .rsi).toNat)
      (by simp [vproW, upd]) (by omega) (by omega) hdx3 hz3)) fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ => ?_)
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans (k3.2.2.trans hw2)
  have hM4 : Frame (vwrR s) s.mem t4.mem :=
    vframe_keep hp.toVPre (k3.2.2.trans hw2) L3.rsp (hm3 ▸ hM2) f4
  have hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rdx, .r8, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this, k3.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb4 => ?_) (fun hb4 => ?_)
  · -- `emLen < hLen + 2`: refused.
    rw [decide_eq_true_eq] at hb4
    refine hfail L4 R4 hw4 hcs4 (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) ?_
    rw [hout]
    exact RsaPss.verify_short _ _ _ _ (by rw [emLen_eq h0, hrl, hGl]; omega)
  rw [decide_eq_false_iff_not] at hb4
  -- The salt length's arguments.
  have hrd4 : t4.rd = s.rd := k4.2.1.trans (k3.2.1.trans hrd2)
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [anyArgs]) (by exact Nat.zero_le 8)
    (anyArgs_ok hp.toVPre L4 hrd4 hM4 R4)) fun t5 ⟨⟨L5, k5, R5, hdx5⟩, f5⟩ => ?_)
  have hM5 : Frame (vwrR s) s.mem t5.mem := vframe_keep hp.toVPre hw4 L4.rsp hM4 f5
  set fixed := decide ((stackArg s 2).setWidth 32 = 0) with hfixed
  set sLen := Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32) with hsLen
  have hsl : sLen = if fixed then some (stackArg s 1).toNat else none := expectedSaltLen_eq _ _
  have hdx5' : t5.gpr .rdx = BitVec.ofNat 64 (sLen.getD 0) := by
    rw [hdx5, hsl, hfixed]
    by_cases hf : (stackArg s 2).setWidth 32 = 0
    · rw [ifp hf, decide_eq_true hf, ifp rfl, Option.getD_some, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ifn hf, decide_eq_false hf]; rfl
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - loV n₀.toNat) ∧
      t.mem = t5.mem) (by
    xrun [ea_sp, L5.rsp, L5.ld (d := sK) (by decide), L5.ld (d := sLo) (by decide), R5.rd (d := sK) 17 rfl (by decide),
      R5.rd (d := sLo) 26 rfl (by decide)]
    simp only [upd, vproW, Nat.reduceEqDiff, ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .rsi).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega) rfl) fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  refine WP.mono (saltFits_ok (H := H) (by omega) t6 (a := (s.gpr .rsi).toNat - loV n₀.toNat)
    (b := BitVec.ofNat 64 (sLen.getD 0)) (by omega) (by omega) hax6 (by rw [k6.gpr (by decide)]; exact hdx5'))
    fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hsl0 : (BitVec.ofNat 64 (sLen.getD 0)).toNat = sLen.getD 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [hsl]; split
    · exact (stackArg s 1).isLt
    · simp
  rw [hsl0] at hc7
  have L7 : Lay t7 (fb s) (stackArg s 3) := L5.congr ((k7.gpr (by decide)).trans (k6.gpr (by decide)))
    (k7.2.2.trans k6.2.2) (by rw [hm7, hm6])
  have hm75 : t7.mem = t5.mem := by rw [hm7, hm6]
  have R7 := hm75 ▸ R5
  have hw7 : t7.wr = frR s :: s.wr := k7.2.2.trans (k6.2.2.trans (k5.2.2.trans hw4))
  have hrd7 : t7.rd = s.rd := k7.2.1.trans (k6.2.1.trans (k5.2.1.trans hrd4))
  have hcs7 : ∀ r ∈ [Reg.r13, .r14, .r15], t7.gpr r = s.gpr r := fun r hr => by
    rw [k7.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  have hM7 : Frame (vwrR s) s.mem t7.mem := hm75 ▸ hM5
  refine WP.ite (M := isa) _ (show isa.eval .b t7 = _ from hc7) (fun hb7 => ?_) (fun hb7 => ?_)
  · -- The salt does not fit: refused.
    rw [decide_eq_true_eq] at hb7
    refine hfail L7 R7 hw7 hcs7 (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) ?_
    rw [hout]
    exact RsaPss.verify_short _ _ _ _ (by rw [emLen_eq h0, hrl, hGl]; omega)
  rw [decide_eq_false_iff_not] at hb7
  -- The encoding.
  have hG := validG hH lk.hash lk.len
  have hlo' : (n₀ :: rest).length - Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) =
      loV n₀.toNat := by rw [emLen_eq h0, hrl]; omega
  refine main_ok hH K lk v hp L7 R7 hw7 hrd7 hcs7 hM7 (lo := loV n₀.toNat)
    (z := 8 * ((s.gpr .rsi).toNat - loV n₀.toNat) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1))
    (fixed := fixed)
    (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd])
    ?_ (by simp [upd]) (by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, hfixed, decide_eq_true_eq])
    (by simp [upd]) (by simp [vproW, upd]) (by simp [vproW, upd])
    (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) hlo (by omega)
    (by rw [hax7]) ?_ hsl
  · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
    rw [maskV_eq rest h0, hEL]
  · rw [hout, RsaPss.verify_bytes lk.G hG (emBits := Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1)
      (emLen := (s.gpr .rsi).toNat - loV n₀.toNat) (bytesAt_length _ _ _) (by rw [bytesAt_length, hrl]) rfl hEL
      (by omega) hlo (by omega), vx, hnB, hrl]


end VG.Proof.RsaPss.X86_64.Pc
