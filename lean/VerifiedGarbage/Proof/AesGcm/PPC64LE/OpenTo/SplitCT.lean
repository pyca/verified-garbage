module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Split
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.CryptTo
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Split
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.CryptTo
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split` is constant time

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split` is
`openWith oneCryptTo`, so its proof is `open`'s (`openWith_ct`), with data
only read (`DataOk`, `dataOk_ok`), and what the comparison of the tags
leaves for the decryption (`SplitX`): the destination, its address on the
stack, at a public address, and the destination apart from the source.
`oneCryptTo` loads the destination from there, and its branches and
addresses are then on the source, the destination and the length
(`oneCryptTo_ct`): the whole blocks by a call of `vg_aes_ctr32_to` with the
same arguments in both runs (`to_rel`), the copy of the last bytes by the
taint analysis, and the last bytes by `open`'s `cryptTail_ct`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-! ## `oneCryptTo` -/

/-- Before `cryptTo`. -/
def ToI (c st w sp : Addr) (R : Nat) (S D : Addr) (n : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ ToIn V sp R S D n s

section
variable {c st w sp : Addr} {R : Nat} {S D : Addr} {n : Nat}

theorem wholeTo_ct : CT (ToI c st w sp R S D n) wholeTo := by
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    V .r28 = BitVec.ofNat 64 R ∧ Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ DataOk (V .r30) (V .r31) s S n ∧
    DataW (V .r29) (V .r30) (V .r31) s D n ∧ (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ ∧
    s.gpr .r6 = S ∧ s.gpr .r7 = BitVec.ofNat 64 (n / 16) ∧ s.gpr .r10 = D
  let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ DataOk (V .r30) (V .r31) s S n ∧
    DataW (V .r29) (V .r30) (V .r31) s D n ∧ (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ ∧
    s.gpr .r3 = V .r29 ∧ s.gpr .r4 = BitVec.ofNat 64 R ∧ s.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧
    s.gpr .r6 = S ∧ s.gpr .r7 = BitVec.ofNat 64 (n / 16) ∧ s.gpr .r8 = D
  refine wholeWith_ct (J₁ := J₁) (J₂ := J₂) ?_ (fun s ⟨V, h29, h30, h31, hs⟩ => ?_)
    (fun s ⟨_, _, _, _, _, _, _, _, hd, _, _, h7, _⟩ => ⟨h7, by have := hd.ok.lt; omega⟩) ?_
    (fun s ⟨V, h29, h30, h31, h28, he, hR, hsr, hd, hsd, h6, h7, h10⟩ => ?_) fun _ => ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26]) (.block splitTo)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.r26, h₂.r26]
  · refine WP.mono (splitTo_ok hs.dst.ok.lt hs.r24 hs.r25 hs.r26) fun s₁ ⟨h6, h7, h10, _, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.r28, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.rounds,
      hs.src.of_eq hk₁.rd hk₁.wr, hs.dst.of_eq hk₁.rd hk₁.wr, hs.sd, h6, h7, h10⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r10, .r28, .r29, .r30, .r31])
        (.block toArgs) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _, _, _, _, _, _, a10⟩
      ⟨_, b29, b30, b31, b28, e₂, _, _, _, _, _, _, b10⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [a10, b10]
    · exact pinK e₁ e₂ (a28.trans b28.symm) (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm)
        (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
  · refine WP.mono (toArgs_ok he h28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hR, hsr.of_eq hk₂.rd hk₂.wr,
      hd.of_eq hk₂.rd hk₂.wr, hsd, a3, a4, a5, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6],
      by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7], by rw [a8, h10]⟩
  · refine to_rel fun s₁ s₂ ⟨⟨V₁, a29, a30, _, he₁, hR, hs₁, hd₁, hsd₁, a3, a4, a5, a6, a7, a8⟩,
      ⟨V₂, b29, b30, _, he₂, _, hs₂, hd₂, hsd₂, b3, b4, b5, b6, b7, b8⟩⟩ => ?_
    have g₁ := toCall_mk he₁ a3 a4 a5 a6 a7 a8 hR hs₁ hd₁ hsd₁
    have g₂ := toCall_mk he₂ b3 b4 b5 b6 b7 b8 hR hs₂ hd₂ hsd₂
    rw [a29, a30] at g₁
    rw [b29, b30] at g₂
    exact ⟨_, _, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTo_ct (L : Lay c st w) : CT (ToI c st w sp R S D n) cryptTo := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, hs⟩ => eval_zero hs.r25 hs.dst.ok.lt)
    (fun _ => CT.skip) fun _ => ?_
  let W₁ : State → Prop := fun s => ∃ V s₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    ToIn V sp R S D n s₀ ∧ WholeOut V sp R S D n s₀ s
  refine CT.seq (J := W₁) wholeTo_ct (fun s ⟨V, h29, h30, h31, hs⟩ =>
    WP.mono (wholeTo_ok hs) fun s' h => ⟨V, s, h29, h30, h31, hs, h⟩) ?_
  refine CT.seq (J := CrM c st w sp R D n 0 (16 * (n / 16))) ?_ (fun s ⟨V, s₀, h29, h30, h31, hs, hw⟩ =>
    WP.mono (copyTail_ok hs hw) fun s' hc =>
      ⟨V, 0, 0, virt s₀.mem S D n, h29, h30, h31, rfl, copied_mid hs hw hc⟩) (cryptTail_ct L)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26]) copyTail
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ =>
    ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r24, h₂.r24]
  · rw [h₁.r25, h₂.r25]
  · rw [h₁.r26, h₂.r26]

/-- Before `oneCryptTo`: the source (`r27`) and its length (`r23`), the
destination at `sp + 120`. -/
def OneToI (c st w sp : Addr) (R : Nat) (S Dst : Addr) (Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r27 = S ∧ V .r23 = Ln ∧
    V .r28 = BitVec.ofNat 64 R ∧ Env V sp s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ DataOk st w s S Ln.toNat ∧
    DataW c st w s Dst Ln.toNat ∧ (⟨S, Ln.toNat⟩ : Region).Disjoint ⟨Dst, Ln.toNat⟩ ∧
    InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 120) 8 ∧ s.mem.readW (sp + BitVec.ofNat 64 120) 64 = Dst

theorem oneCryptTo_ct (L : Lay c st w) {Dst : Addr} {Ln : BitVec 64} :
    CT (OneToI c st w sp R S Dst Ln) oneCryptTo := by
  refine CT.seq (J := ToI c st w sp R S Dst Ln.toNat) ?_
    (fun s ⟨V, a29, a30, a31, a27, a23, a28, he, hR, hs, hd, hsd, hi, hv⟩ => ?_) (cryptTo_ct L)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23, .r27]) (.block dataTo)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a27, a23, _, e₁, _⟩ ⟨_, _, _, _, b27, b23, _, e₂, _⟩ =>
      ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a27, b27]
  · refine WP.mono (dataTo_ok he hi hv) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_
    refine ⟨V, a29, a30, a31, he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₁.sp k₁.rd k₁.wr, by rw [a24, a27], by rw [a25, a23], a26, a28,
      hR, by rw [a30, a31]; exact hs.of_eq k₁.rd k₁.wr, by rw [a29, a30, a31]; exact hd.of_eq k₁.rd k₁.wr, hsd⟩

end

/-! ## `vg_aes_gcm_open_split` -/

/-- After the entry (and `r25` restored), what the pieces up to the
comparison of the tags need. -/
theorem split_one {t₀ s : State} (h : splitPre t₀) (h1 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s)
    (h19 : s.gpr .r19 = stackArg t₀ 1) :
    OneOP (fun _ st w s D n => DataOk st w s D n) (t₀.gpr .r3) (stackArg t₀ 2) t₀.sp (t₀.gpr .r4).toNat
      (t₀.gpr .r5) (t₀.gpr .r6).toNat (t₀.gpr .r7) (t₀.gpr .r8) (t₀.gpr .r9) (t₀.gpr .r10) (stackArg t₀ 0)
      (stackArg t₀ 1) s := by
  have hp := HeadPre.of_split h
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine ⟨⟨s.gpr, h1.r29, h1.r30, h1.r31, by rw [h1.r28]; exact toN, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hp.ctx hp.w, ?_, ?_, ?_⟩, h1.r20, h19, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.nonce, (t₀.gpr .r6).isLt, hp.fn,
      hp.dnW.sub_right (Lay.wSub (by decide)), hp.dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.aad, (t₀.gpr .r8).isLt, hp.fa,
      hp.daW.sub_right (Lay.wSub (by decide)), hp.daW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.data, (t₀.gpr .r10).isLt, hp.fd,
      hp.ddW.sub_right (Lay.wSub (by decide)), hp.ddW⟩
  · rw [hk₁.rd, hk₁.wr]; exact hp.tag

/-- What the comparison of the tags leaves for `oneCryptTo`, from `t₀`. -/
def SplitX (t₀ s : State) : Prop :=
  DataW (t₀.gpr .r3) (stackArg t₀ 2 + BitVec.ofNat 64 16) (stackArg t₀ 2) s (stackArg t₀ 3) (t₀.gpr .r10).toNat ∧
    (⟨t₀.gpr .r9, (t₀.gpr .r10).toNat⟩ : Region).Disjoint ⟨stackArg t₀ 3, (t₀.gpr .r10).toNat⟩ ∧
    InRegions (s.rd ++ s.wr) (t₀.sp + BitVec.ofNat 64 120) 8 ∧
    s.mem.readW (t₀.sp + BitVec.ofNat 64 120) 64 = stackArg t₀ 3

theorem split_x {t₀ s₄ s₉ : State} (h : splitPre t₀) (h4 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₄)
    (om : OpenMid t₀ s₄ s₉) : SplitX t₀ s₉ := by
  have hh := h
  obtain ⟨hrd, hwr, _, _, _, _, _, _, dcD, dsD, dDW, _, _, _, _, _, _, fD, _, _⟩ := hh
  have rd₀ : s₉.rd = t₀.rd := om.rd.trans h4.en.keeps.rd
  have wr₀ : s₉.wr = t₀.wr := om.wr.trans h4.en.keeps.wr
  have hw : Covers [⟨stackArg t₀ 3, (t₀.gpr .r10).toNat⟩] s₉.wr := by rw [wr₀, hwr]; exact covers_mem (by simp)
  refine ⟨⟨⟨covers_left hw, (t₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩, dsD,
    ?_, dst_at h om.frame⟩
  rw [rd₀, wr₀]
  have hA : Covers [args t₀ 4] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
  rwa [stackArgAddr_0, add_ofNat_assoc] at this

theorem split_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    ConstantTime isa splitPPC64LE.pre splitPPC64LE.pub openSplit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : splitPre σ₁ := h₁
  obtain ⟨_, _, dcW, _, _, _, _, _, _, _, _, fc, _, _, _, _, fW, _, _, hR⟩ := h₁'
  let I₀ : State → Prop := fun s => splitPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome ∧
    stackArg s 3 = stackArg σ₁ 3
  have i₁ : I₀ σ₁ := ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨I₀, i₁, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm,
    (qa 0 (by decide)).symm, (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qres hR).symm,
    (qa 3 (by decide)).symm⟩, ?_⟩
  have L₀ := oneLay fc fW dcW
  refine openWith_ct σ₁ I₀ i₁ dataOk_ok (X := SplitX σ₁)
    (fun s ⟨hp, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres, _⟩ =>
      ⟨HeadPre.of_split hp, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩)
    (fun t₀ s ht h1 h19 => split_one ht.1 h1 h19)
    (fun t₀ s₄ s₉ ht h4 om => ?_)
    ((oneCryptTo_ct L₀ (Dst := stackArg σ₁ 3) (Ln := σ₁.gpr .r10)).mono
      fun s ⟨⟨V, a, b, d, e, _, _, _, j, k, he, _, _, hD⟩, hdw, hsd, hi, hv⟩ =>
        ⟨V, a, b, d, j, k, e, he, hR, hD, hdw, hsd, hi, hv⟩)
    (fun s ⟨⟨V, a, b, d, e, _, _, _, j, k, he, _, _, hD⟩, hdw, hsd, hi, hv⟩ =>
      have hD' : DataOk (stackArg σ₁ 2 + BitVec.ofNat 64 16) (stackArg σ₁ 2) s (σ₁.gpr .r9)
          (σ₁.gpr .r10).toNat := hD
      WP.mono (oneCryptTo_ok (L₀.v a b d) he e hR (by rw [b, d, j, k]; exact hD')
        (by rw [a, b, d, k]; exact hdw) (by rw [j, k]; exact hsd) hi hv (icb := 0))
        fun s' oc => ⟨by rw [oc.env.r31, d], oc.env.sp⟩)
    (fun t₀ s₄ ht h4 h19 hok => WP.mono (split_good ht.1 h4 h19 hok) fun s' oo => ⟨oo.r31, oo.sp⟩)
  obtain ⟨hp, e3, _, _, _, _, _, e9, e10, esp, _, _, ea2, _, ea3⟩ := ht
  have x := split_x hp h4 om
  unfold SplitX at x ⊢
  rw [e3, e9, e10, ea2, ea3, esp] at x
  exact x

end VG.Proof.AesGcm.PPC64LE
