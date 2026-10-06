import VerifiedGarbage.Proof.RsaOaep.X86_64.DecMain
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect

/-!
# RSAES-OAEP decryption on x86-64: correctness

The frame, the prologue, the private operation, its result to its slot and
the check of `k` (zeros to `out` and `*msg_len` if the operation failed or
`k` is too small, the decoding otherwise): `dec_correct`.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl privStack)

/-- The private operation's result to its slot, zero-extended, and the
check of `k`. -/
theorem resK_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hk1 : k < 2 ^ 32) (hD : Hm.D < 2 ^ 20) :
    WP isa (.block (([.mov32 .rax (.reg .rax), .store (sp sR) .rax] : List Instr) ++ chkK Hm)) u fun u' =>
      Keep [.rax] u u' ∧ Lay u' F S ∧ Rep u'.mem F S V (upd W 30 (((u.gpr .rax).setWidth 32).setWidth 64)) ∧
      u'.cf = some (decide (k < 2 * Hm.D + 2)) := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun x => x.mem = u.mem.writeW (off F sR)
    (((u.gpr .rax).setWidth 32).setWidth 64)) ?_ rfl) fun x ⟨hmx, kx⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sR) (by decide)]
  have R' : Rep x.mem F S V (upd W 30 (((u.gpr .rax).setWidth 32).setWidth 64)) := by
    rw [hmx]; exact R.wf L.geo (k := 30) (by decide) _
  have L' : Lay x F S := L.of_rep' R R' (by simp [upd]) (kx.gpr (by decide)) kx.2.2
  refine WP.mono (chkK_ok L' R' (by simp only [upd]; exact hk) hk1 hD) fun u' ⟨k2, hm2, _, hcf⟩ =>
    ⟨(kx.trans k2).mono (by decide), L'.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), hm2 ▸ R', hcf⟩

theorem decKs_iff {k : Nat} (h : k ∈ decKs) : k = 14 ∨ (21 ≤ k ∧ k ≤ 29) := by
  simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ArgsD_privW (s : State) : ArgsD s (privW s) := fun j hj => by
  have := decKs_iff hj
  simp only [privW, upd, show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega,
    show j ≠ 4 by omega, show j ≠ 5 by omega, show j ≠ 6 by omega, show j ≠ 7 by omega, show j ≠ 8 by omega,
    show j ≠ 9 by omega, show j ≠ 10 by omega, show j ≠ 11 by omega, show j ≠ 12 by omega,
    show j ≠ 13 by omega, ↓reduceIte]

/-! ## The end -/

/-- What the function's caller sees: from a state in the frame with `out`
and `*msg_len` written as `o` says. -/
theorem decEnd_ok {s s₂ : State} (hp : DPre s) (he : EnvD s s₂) {o : Spec.Rsa.Outcome}
    (hw : Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat
      ((s₂.gpr .rax).setWidth 32) o) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧
      (abiPreserved s (freed frameBytes s₂) ∧
        Spec.RsaOaep.writtenDecrypt (freed frameBytes s₂).mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat
          (((freed frameBytes s₂).gpr .rax).setWidth 32) o) := by
  refine ⟨he.rsp, by rw [he.wr, hp.wr], ⟨fun r hr => ?_, ?_, he.mx⟩, hw⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show s₂.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else s₂.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact he.cs r hr hr'
  · have := hp.sp1; have := hp.sp2
    refine Frame.readW he.fr (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have := Offset.disjoint_below (s.gpr .rsp) (n := decStack) (d := 0) (k := 8)
        (by unfold decStack privStack Impl.RsaOaep.X86_64.frameBytes; omega)
      simpa only [stkD, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.dRO
    · exact hp.dRM
    · exact hp.dRs

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH KH hG KG mH mG in
theorem dec_correct (v : PrivImpl) (s : State) (h : (decK mH.G mG.G).pre s) :
    ∃ t s', Exec isa (decrypt Hl.stream Gm.stream v.name v.code) s t s' ∧ abiPreserved s s' ∧
      (decK mH.G mG.G).post s s' := by
  have hp : DPre s := DPre.of mH.G mG.G h
  have hk1 := hp.lv.1; have hk2 := hp.lv.2
  have hD := hH.hD0; have hDN := hH.hDN; have hN := hH.N_le
  have hlen : mH.G.len = Hl.D := mH.len
  have hsD : Hl.stream.D = Hl.D := rfl
  suffices hw : WP isa (decrypt Hl.stream Gm.stream v.name v.code) s
      fun s' => abiPreserved s s' ∧ (decK mH.G mG.G).post s s' by
    obtain ⟨t, s', he, hq⟩ := hw; exact ⟨t, s', he, hq⟩
  refine wp_alloc (by have := hp.sp1; unfold decStack privStack at this; unfold frameBytes at *; omega) ?_
  have hct : (Spec.Rsa.bytesAt s.mem (stackArg s 13) (s.gpr .r8).toNat).length =
      (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length := by simp [Spec.Rsa.bytesAt]
  have fin : ∀ s₂, EnvD s s₂ → Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat
      ((s₂.gpr .rax).setWidth 32)
      (decOut mH.G mG.G (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) (privOutD s)) →
      s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧
        (abiPreserved s (freed frameBytes s₂) ∧ (decK mH.G mG.G).post s (freed frameBytes s₂)) :=
    fun s₂ he hw => by
      refine decEnd_ok hp he ?_
      rw [decrypt_eq hct]; exact hw
  unfold decBody seqs seqs seqs
  refine WP.seq (WP.mono (decHead_ok hp) fun t0 h0 => ?_)
  refine WP.seq (WP.mono (privD_call v hp h0) fun t1 ⟨he1, L1, R1, hw1⟩ => ?_)
  have hW1 : ArgsD s (privW s) := ArgsD_privW s
  obtain ⟨-, w21, -, w23, -, -, -, -, -, w29⟩ := hW1.w
  have w23' : privW s 23 = BitVec.ofNat 64 (s.gpr .r8).toNat := by
    rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wp_good (block_good _ rfl) (resK_ok (Hm := Hl.stream) L1 R1 w23' (by omega) (by omega)))
    fun t2 ⟨⟨k2, L2, R2, hcf2⟩, sp2, mx2, f2⟩ => ?_)
  have he2 : EnvD s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  generalize hW2 : upd (privW s) 30 (((t1.gpr .rax).setWidth 32).setWidth 64) = W2 at R2
  have hA2 : ArgsD s W2 := hW1.of fun j hj => by
    rw [← hW2]; simp only [upd]
    rw [ifn (by simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at hj; omega)]
  have h30 : W2 30 = ((t1.gpr .rax).setWidth 32).setWidth 64 := by rw [← hW2]; simp [upd]
  -- The private operation's outcome, in our working space and slot 30.
  have hres : ResD (fun o => t1.mem (off (stackArg s 15) o)) W2 (s.gpr .r8).toNat (privOutD s) := by
    revert hw1
    cases privOutD s with
    | ok em =>
      rintro ⟨hr, hb⟩
      refine ⟨by rw [h30, hr]; rfl, ?_⟩
      rw [← hb]; simp only [Spec.Rsa.bytesAt, off]
      refine List.map_congr_left fun i _ => ?_
      rw [show oEm = 0 from rfl, Nat.zero_add, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    | invalid => rintro ⟨hr, -⟩; show W2 30 = 0; rw [h30, hr]; rfl
    | fault => rintro ⟨hr, -⟩; show W2 30 = 2; rw [h30, hr]; rfl
  have hlenO : ∀ em, privOutD s = .ok em → em.length = (s.gpr .r8).toNat := fun em he => by
    rw [he] at hw1; rw [← hw1.2]; simp [Spec.Rsa.bytesAt]
  refine WP.ite (M := isa) _ (show isa.eval .b t2 = _ from hcf2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    obtain ⟨-, x21, -, x23, -, -, -, -, -, x29⟩ := hA2.w
    have hout : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by simp [outR, hp.hsi]
    have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega)
    have aO : Apart (fb s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by
      rw [hout]; exact ⟨hp.dKO.sub_left (frame_subD s), hp.dOs.symm.sub_left sS, hp.dKO.sub_left (ret_subD s)⟩
    have aM : Apart (fb s) (stackArg s 15) (mlR s) :=
      ⟨hp.dKM.sub_left (frame_subD s), hp.dMs.symm.sub_left sS, hp.dKM.sub_left (ret_subD s)⟩
    have dom : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ ⟨s.gpr .rdx, 8⟩ := by
      have := hp.dOM; rw [hp.hsi] at this; exact this
    refine WP.mono (wp_good decFail_good (decFail_ok L2 R2 (o := s.gpr .rdi) (pm := s.gpr .rdx)
      (k := (s.gpr .r8).toNat) x21 x29 (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) hk2 (by rw [he2.wr, hout]; simp) (by have := hp.wO; rw [hp.hsi] at this; exact this) aO
      (by rw [he2.wr]; simp [mlR]) hp.wM aM dom))
      fun t3 ⟨⟨L3, k3, R3, hz3, hm3, _, hax3⟩, sp3, mx3, f3⟩ => fin t3 (he2.step k3.2.1 k3.2.2 sp3
        (keep_cs3 k3 (by decide)) mx3 f3) ?_
    rw [decOut_short hlenO (by rw [hlen, ← hsD]; exact hb)]
    revert hres hlenO
    cases privOutD s with
    | ok em =>
      rintro ⟨hr, -⟩ -
      refine ⟨by rw [hax3, faultW, hr]; rfl, hz3, hm3⟩
    | invalid =>
      intro hr _
      refine ⟨by rw [hax3, faultW, show W2 30 = 0 from hr]; rfl, hz3, hm3⟩
    | fault =>
      intro hr _
      refine ⟨by rw [hax3, faultW, show W2 30 = 2 from hr]; rfl, hz3, hm3⟩
  · rw [decide_eq_false_iff_not] at hb
    exact WP.mono (decMain_ok hH KH hG KG mH mG hp he2 L2 R2 hA2 (by omega) hres) fun t3 ⟨he3, hw3⟩ =>
      fin t3 he3 hw3

end VG.Proof.RsaOaep.X86_64
