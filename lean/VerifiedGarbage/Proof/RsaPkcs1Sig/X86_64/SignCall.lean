import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignEntry
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the call of `vg_rsa_private_checked`

The private operation, for an implementation `v` of the CRT (`CrtImpl`), is
`vg_rsa_private_checked`'s code (`privCode v`), which has a frame of its own:
it uses 3256 bytes of stack (`privCode_depth`). Its arguments
(`callArgs_ok`) and the call (`priv_call`), which signs `EM` into `out`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract code_correct code_spSafe)

/-! ## The private operation -/

/-- The names of the public operation `vg_rsa_private_checked` calls, as in
`Generic/RsaPrivateCrt/X86_64/Rsa.lean`. -/
def pcName (v : CrtImpl) : String := Spec.Rsa.publicPrecomputeApi.name ++ v.montSuffix
def pdName (v : CrtImpl) : String := v.pubOp.name

/-- `vg_rsa_private_checked`'s name and code, for `v`. -/
def privName (v : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix
def privCode (v : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.code v.name v.code (pcName v) v.pc (pdName v) v.pubOp.code

theorem privCode_depth (v : CrtImpl) : (privCode v).x86_64Depth = 3256 := by
  simp only [privCode, Impl.Rsa.X86_64.PrivChecked.code, Impl.Rsa.X86_64.PrivChecked.body,
    Impl.Rsa.X86_64.PrivChecked.check, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp v.nosp, v.depth, x86_64Depth_noSp v.pcNosp,
    v.pcDepth, x86_64Depth_noSp v.pubOp.nosp, v.pubOp.depth, X86_64.Instr.frameBytes,
    Impl.Rsa.X86_64.PrivChecked.frameBytes, Impl.Rsa.X86_64.PrivChecked.cmpLoop,
    Impl.Rsa.X86_64.PrivChecked.releaseLoop]
  rfl

/-- The call of `vg_rsa_private_checked`: `out` holds the signature of
`EM`, or zeros. -/
theorem priv_call (v : CrtImpl) {s t : State} (hp : PreS s) (he : Env s t)
    (hw : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call (privName v) (privCode v)) t fun t' => Env s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)) ∧
      (∀ d n, d + n ≤ frameBytes → ∀ i < n,
        t'.mem (off (fb s) d + BitVec.ofNat 64 i) = t.mem (off (fb s) d + BitVec.ofNat 64 i)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := priv_covers hp he
  have hd := privCode_depth v
  unfold privCode at hd
  refine WP.call_sp_mx (k := chkContract) (code_correct v (pcName v) (pdName v))
    (SpSafe.of_all (code_spSafe v _ _)) (by rw [hd]; decide)
    (priv_pre hp he.rsp hw hdi hsi hdx hcx h8 h9) hc hcw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = callArg s i :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega)).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega)
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr, below_kb]; exact .inl (Region.sub_prefix (by decide))
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  have hEM : Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) oEM) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (callEntry_frame he.rsp).bytes
      (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩) (fun r hr => ?_) (by dsimp only; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, below_kb, fb_kb, off_off]
    exact (Offset.base_disjoint (kb s) (e := 3264 + oEM) (n := (s.gpr .rcx).toNat) (k := 3264) (by omega)
      (by have := (kb_toNat hp).1; unfold oEM; unfold sigStack at this; omega)).symm
  simp only [chkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE 0 (by decide), callArg, hm₂, hg₂ .rax (by decide),
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 6 (by decide) : stackArg _ 8 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega),
    hEM, b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega), b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega),
    ← hp.hdpl, b hp.dKdp hp.dOdp hp.ddps.symm (by have := hp.wDp; omega), hp.hdpl,
    ← hp.hdql, b hp.dKdq hp.dOdq hp.ddqs.symm (by have := hp.wDq; omega), hp.hdql,
    ← hp.hqil, b hp.dKqi hp.dOqi hp.dqis.symm (by have := hp.wQi; omega), hp.hqil] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, fun d n hd i hi => ?_, hcs, hmx⟩
  · simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (Ver.sub_refl _))
    · exact .inr (.inr (Ver.sub_refl _))
    · rw [below_kb]; exact .inl (Region.sub_prefix (by decide))
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sOut
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sOl
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sN
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sK
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sE
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sEl
  · have := (fb_toNat hp).1
    exact hf.bytes (R := ⟨off (fb s) d, n⟩) (frame_apart hp hd) (by dsimp only; unfold frameBytes at hd; omega) hi

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
