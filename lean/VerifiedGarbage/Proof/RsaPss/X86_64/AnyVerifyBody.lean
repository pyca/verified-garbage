module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyChecks
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Impl.RsaPss.X86_64.AnyHash (emLenAny saltFitsAny)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash}

/-- The modulus' first byte. -/
theorem vn0_okA {s t : State} (hp : VPreA G s) (L : Lay t (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 4) V W) (h18 : W 18 = s.gpr .rdi) (hrd : t.rd = s.rd)
    (hf : Frame (vwrRA s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdi) = s.mem (s.gpr .rdi) := by
    have := hf.bytes (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) (vin_apartA hp.dKn hp.dns)
      (by dsimp only; have := hp.wN; omega) (i := 0) (by dsimp only; omega)
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdi) 1 := by
    rw [hrd]
    apply hp.hrd.left
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdi)).isLt; omega)]
  exact ⟨rfl, rfl⟩

theorem vfail_doneA {H G : Spec.Mgf1.Hash} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 4)) (R : Rep t.mem (fb s) (stackArg s 4) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hf : verifyOutA H G s = false) :
    WP isa verifyFail t (DoneA H G s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [verifyFail]
  have R' : Rep t'.mem (fb s) (stackArg s 4) V W := hm ▸ R
  refine ⟨false, ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw, fun r hr => ?_, ?_, ?_, ?_, ?_⟩,
    fun _ => hf.symm⟩
  · rw [k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide), hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hax]; rfl

theorem vrestore_okA {H G : Spec.Mgf1.Hash} {s t : State} (d : DoneA H G s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧
      (validCacheA s → ((freedF t').gpr .rax).setWidth 32 = if verifyOutA H G s then 1 else 0) := by
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
    rw [← hb hc]
    exact D.out

theorem code_okA {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H)
    (lk : MgfLink H hH) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG) (v : PublicImpl)
    {s : State} (h : verifyAnyK.pre s) (hsk : vhsel s = kh) (hsg : vmsel s = g)
    (hHs : Spec.HashId.mgf1 kh = some lk.G) (hGs : Spec.HashId.mgf1 g = some lkG.G) :
    WP isa (AnyHash.verify hs v.name v.code) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      verifyAnyK.post s s' := by
  have hp := VPreA.of lk.G h (by rw [hsk]; exact hHs)
  have hF := vfb_toNatA hp
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl : lk.G.len = H.D := lk.len
  have h15v : s.gpr .r9 = BitVec.ofNat 64 H.D := by
    rw [← lk.len, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have e8 : stackArg s 8 = BitVec.ofNat 64 kh := by rw [← hsk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have e9 : stackArg s 9 = BitVec.ofNat 64 g := by rw [← hsg, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine wp_frame (by have := hp.sp1; unfold verifyStack frameBytes at *; omega) ?_
  rw [AnyHash.verifyBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (verifyPro_okA hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  have hM1 : Frame (vwrRA s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono (vn0_okA hp L1 R1 (by simp [vproWA, upd]) k1.2.1 hM1) fun t2 ⟨k2, hm2, hax2, hz2⟩ => ?_
  have L2 : Lay t2 (fb s) (stackArg s 4) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 4) _ (vproWA s) := hm2 ▸ R1
  have hM2 : Frame (vwrRA s) s.mem t2.mem := hm2 ▸ hM1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := DoneA lk.G lkG.G s) ?_ fun t3 D => WP.mono (vrestore_okA D)
    fun t' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun H' G' hH' hG' hc => by
      rw [hsk, hHs] at hH'
      rw [hsg, hGs] at hG'
      cases hH'; cases hG'
      rw [h4 hc, verifyOutA, ← hp.hdl]⟩)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdi) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdi + 1) ((s.gpr .rsi).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega)
  have hrl : (n₀ :: rest).length = (s.gpr .rsi).toNat := by
    rw [← hnB]; simp [Spec.Rsa.bytesAt]
  have hout : verifyOutA lk.G lkG.G s = Spec.RsaPss.verify lk.G lkG.G (n₀ :: rest)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
      (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)) := by rw [verifyOutA, hnB]
  have hfail : ∀ {t : State} {V : Nat → Byte} {W : Nat → BitVec 64}, Lay t (fb s) (stackArg s 4) →
      Rep t.mem (fb s) (stackArg s 4) V W → t.wr = frR s :: s.wr →
      (∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r) →
      W 41 = s.gpr .rbx → W 42 = s.gpr .rbp → W 43 = s.gpr .r12 → verifyOutA lk.G lkG.G s = false →
      WP isa verifyFail t (DoneA lk.G lkG.G s) := fun L R hw hcs a b c d => vfail_doneA L R hw hcs a b c d
  refine WP.ite (M := isa) _ (show isa.eval .e t2 = _ from hz2) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine hfail L2 R2 hw2 hcs2 (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd]) ?_
    rw [hout, h0]; exact RsaPss.Any.verify_zero ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hEL := emLen_eq (rest := rest) h0
  rw [hrl] at hEL
  have hlo : loV n₀.toNat ≤ 1 := by unfold loV; split <;> omega
  -- `smear(n₀ >> 1)`.
  refine WP.seq (WP.mono (smear_ok t2 (x := n₀.toNat) n₀.isLt hb hax2) fun t3 ⟨k3, hm3, hdx3, hz3⟩ => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 4) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 4) _ (vproWA s) := hm3 ▸ R2
  -- `emLen`, the mask and `lo`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [emLenAny]) (by exact Nat.zero_le 8)
    (emLenAny_ok (D := H.D) (by omega) L3 R3 (x := n₀.toNat) (k := (s.gpr .rsi).toNat)
      (by simp [vproWA, upd]) (by simp [vproWA, upd, h15v]) (by omega) (by omega) hdx3 hz3))
    fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ => ?_)
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans (k3.2.2.trans hw2)
  have hM4 : Frame (vwrRA s) s.mem t4.mem :=
    vframe_keepA hp (k3.2.2.trans hw2) L3.rsp (hm3 ▸ hM2) f4
  have hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rdx, .r8, .rax, .r9] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this, k3.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb4 => ?_) (fun hb4 => ?_)
  · -- `emLen < hLen + 2`: refused.
    rw [decide_eq_true_eq] at hb4
    refine hfail L4 R4 hw4 hcs4 (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd]) ?_
    rw [hout]
    exact RsaPss.Any.verify_short _ _ _ _ _ (by rw [emLen_eq h0, hrl, hGl]; omega)
  rw [decide_eq_false_iff_not] at hb4
  -- The salt length's arguments.
  have hrd4 : t4.rd = s.rd := k4.2.1.trans (k3.2.1.trans hrd2)
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [AnyHash.anyArgs]) (by exact Nat.zero_le 8)
    (anyArgs_okA hp L4 hrd4 hM4 R4)) fun t5 ⟨⟨L5, k5, R5, hdx5⟩, f5⟩ => ?_)
  have hM5 : Frame (vwrRA s) s.mem t5.mem := vframe_keepA hp hw4 L4.rsp hM4 f5
  set fixed := decide ((stackArg s 2).setWidth 32 = 0) with hfixed
  set sLen := Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32) with hsLen
  have hsl : sLen = if fixed then some (stackArg s 3).toNat else none := expectedSaltLen_eq _ _
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
    simp only [upd, vproWA, Nat.reduceEqDiff, ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .rsi).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega) rfl) fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  have L6 : Lay t6 (fb s) (stackArg s 4) := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine WP.mono (saltFitsAny_ok (D := H.D) L6 (hm6 ▸ R5) (by simp [vproWA, upd, h15v])
    (a := (s.gpr .rsi).toNat - loV n₀.toNat)
    (b := BitVec.ofNat 64 (sLen.getD 0)) (by omega) (by omega) hax6 (by rw [k6.gpr (by decide)]; exact hdx5'))
    fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hsl0 : (BitVec.ofNat 64 (sLen.getD 0)).toNat = sLen.getD 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [hsl]; split
    · exact (stackArg s 3).isLt
    · simp
  rw [hsl0] at hc7
  have L7 : Lay t7 (fb s) (stackArg s 4) := L5.congr ((k7.gpr (by decide)).trans (k6.gpr (by decide)))
    (k7.2.2.trans k6.2.2) (by rw [hm7, hm6])
  have hm75 : t7.mem = t5.mem := by rw [hm7, hm6]
  have R7 := hm75 ▸ R5
  have hw7 : t7.wr = frR s :: s.wr := k7.2.2.trans (k6.2.2.trans (k5.2.2.trans hw4))
  have hrd7 : t7.rd = s.rd := k7.2.1.trans (k6.2.1.trans (k5.2.1.trans hrd4))
  have hcs7 : ∀ r ∈ [Reg.r13, .r14, .r15], t7.gpr r = s.gpr r := fun r hr => by
    rw [k7.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  have hM7 : Frame (vwrRA s) s.mem t7.mem := hm75 ▸ hM5
  refine WP.ite (M := isa) _ (show isa.eval .b t7 = _ from hc7) (fun hb7 => ?_) (fun hb7 => ?_)
  · -- The salt does not fit: refused.
    rw [decide_eq_true_eq] at hb7
    refine hfail L7 R7 hw7 hcs7 (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd]) ?_
    rw [hout]
    exact RsaPss.Any.verify_short _ _ _ _ _ (by rw [emLen_eq h0, hrl, hGl]; omega)
  rw [decide_eq_false_iff_not] at hb7
  -- The encoding.
  have hGv := validG hG lkG.hash lkG.len
  refine main_okA hkh hg hl ht hkH hH K lk hG KG lkG v hp L7 R7 hw7 hrd7 hcs7 hM7 (lo := loV n₀.toNat)
    (z := 8 * ((s.gpr .rsi).toNat - loV n₀.toNat) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1))
    (fixed := fixed)
    (by simp [vproWA, upd, h15v])
    (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd])
    ?_ (by simp [upd]) (by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, hfixed, decide_eq_true_eq])
    (by simp [upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd])
    (by simp [vproWA, upd]) (by simp [vproWA, upd]) (by simp [vproWA, upd])
    (by simp [vproWA, upd, e8]) (by simp [vproWA, upd, e9]) hlo (by omega)
    (by rw [hax7]) ?_ hsl
  · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
    rw [maskV_eq rest h0, hEL]
  · rw [hout, RsaPss.Any.verify_bytes lk.G lkG.G hGv (emBits := Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1)
      (emLen := (s.gpr .rsi).toNat - loV n₀.toNat) (bytesAt_length _ _ _) (by rw [bytesAt_length, hrl]) rfl hEL
      (by omega) hlo (by omega), vxA, hnB, hrl]

end VG.Proof.RsaPss.X86_64.Any
