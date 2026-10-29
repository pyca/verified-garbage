module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.CopyBytes
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.EncodeEq
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect

/-!
# EMSA-PSS's encoding on x86-64: correctness

`enc_body`: from the entry state, the body of the frame leaves `rax` and
`em` as `Spec.RsaPss.encode` says, with the callee-saved registers in their
slots; `enc_correct`: `encode` meets `encK` and keeps the callee-saved
registers, its return address and MXCSR's control bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {G : Spec.Mgf1.Hash}

variable (G) in
/-- What `encK.post` asks for. -/
def encOut (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (s.gpr .r9).toNat

variable (G) in
/-- The outcome, from the memory and `rax`. -/
def OutOk (s : State) (m : Mem) (rax : BitVec 64) : Prop :=
  match encOut G s with
  | some e => rax.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = e
  | none => rax.setWidth 32 = 0

variable (G) in
/-- Before the epilogue: the outcome, the saved registers in their slots. -/
structure EDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : OutOk G s t.mem (t.gpr .rax)

/-- A refusal: 0. -/
theorem ret0_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 0)) (R : Rep t.mem (fb s) (stackArg s 0) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hn : encOut G s = none) :
    WP isa ret0 t (EDone G s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [ret0]
  have R' : Rep t'.mem (fb s) (stackArg s 0) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw,
    fun r hr => (k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans (hcs r hr), ?_, ?_, ?_, ?_⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · simp only [OutOk, hn, hax]; rfl

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

/-- The copy of `EM` to `em`. -/
theorem copyOut_ok {s u : State} (hp : Pre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W) (hw : u.wr = frR s :: s.wr)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rsi) (hk1 : 1 ≤ (s.gpr .rsi).toNat) :
    WP isa copyOut u fun u' => Lay u' (fb s) (stackArg s 0) ∧ Keep [.rsi, .rdi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem (fb s) (stackArg s 0) V W ∧
      Spec.Rsa.bytesAt u'.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (List.range (s.gpr .rsi).toNat).map (fun i => V (oEm + i)) ∧
      (∀ x, ¬ (outR s).Contains x 1 → u'.mem x = u.mem x) := by
  have hk2 := hp.k2
  have hF := fb_toNat hp
  have G' := hp.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .r10, .r8] (Q := fun v => v.gpr .rsi = off (stackArg s 0) oEm ∧
      v.gpr .rdi = s.gpr .rdi ∧ v.gpr .r10 = BitVec.ofNat 64 (s.gpr .rsi).toNat ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₁₀, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [copyOut, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide), hs, R.rd (d := sOut) 16 rfl (by decide),
      R.rd (d := sK) 17 rfl (by decide), h16, h17, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
    simp
  have Lv : Lay v (fb s) (stackArg s 0) := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  have hO : (outR s).Disjoint ⟨stackArg s 0, oRsa⟩ :=
    hp.dOs.sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega))
  have hOF : (outR s).Disjoint ⟨fb s, frameBytes⟩ := (hp.dKo.sub_left (frame_sub s)).symm
  refine WP.mono (copyBytes_ok (p := s.gpr .rdi) (q := off (stackArg s 0) oEm) (n := (s.gpr .rsi).toNat)
    (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀) (by omega) hp.wO
    (by rw [hkv.2.2, hw, hp.hwr]; simp) (fun i hi => by
      rw [off_plus]; exact Lv.sld8 (d := oEm + i) (by unfold oEm oRsa; omega))
    (fun i hi hc => hO _ hc (by
      rw [off_plus]; exact (cS _ (o := oEm + i) (n := 1) (by unfold oEm oRsa; omega)).byte
        (by rw [BitVec.sub_self]; decide)))
    h₂ h₁ h₃) fun w ⟨kw, hmw⟩ => ?_
  have hout : ∀ x, ¬ (outR s).Contains x 1 → w.mem x = u.mem x := fun x hx => by
    simp only [outR] at hx; rw [hmw, ifn hx, hm]
  have Rw : Rep w.mem (fb s) (stackArg s 0) V W := R.of_outside hout hO hOF G'
  refine ⟨Lv.of_rep (hm ▸ R) Rw (kw.gpr (by decide)) kw.2.2, (hkv.trans kw).mono (by decide), Rw, ?_, hout⟩
  rw [bytesAt_copied hp.wO (by rw [hm] at hmw; exact hmw), bytesAt_off]
  exact List.map_congr_left fun i hi => R.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega)

/-- An input's bytes, unchanged. -/
theorem bytesF_eq {s : State} {m : Mem} (hM : Frame (wrR s) s.mem m) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrR s, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    (List.range n).map (bytesF m p) = Spec.Rsa.bytesAt s.mem p n :=
  bytesAt_frame hM hd hn

include hH K in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {s u : State} (hp : Pre lk.G s) {V : Nat → Byte}
    {W : Nat → BitVec 64} (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r)
    (hM : Frame (wrR s) s.mem u.mem)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rsi)
    (h25 : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat)))
    (h26 : W 26 = 0) (h37 : W 37 = s.gpr .rdx) (h39 : W 39 = s.gpr .rcx) (h40 : W 40 = s.gpr .r8)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12)
    (hfit : H.D + (s.gpr .r8).toNat + 2 ≤ (s.gpr .rsi).toNat)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - (H.D + 2))) :
    WP isa (encMain H) u (EDone lk.G s) := by
  have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hG := validG hH lk.hash lk.len
  have dg : ∀ r ∈ wrR s, (⟨s.gpr .rdx, H.D⟩ : Region).Disjoint r := by
    rw [hD]; exact in_apart hp.dKdg hp.dOdg hp.ddgs
  have sa : ∀ r ∈ wrR s, (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint r :=
    in_apart hp.dKsa hp.dOsa hp.dsas
  have hdg : (s.gpr .rdx).toNat + H.D ≤ 2 ^ 64 := by rw [hD]; exact hp.wDg
  have hsa := hp.wSa
  rw [encMain]
  simp only [seqs]
  -- The encoding.
  refine WP.seq (WP.mono (WP.keepIn (signEnc_safe hH K) (by rw [signEnc_xd K])
    (signEnc_ok hH K lk L R (k := (s.gpr .rsi).toNat) (lo := 0) (sl := (s.gpr .r8).toNat)
      (c := (0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat))
      (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h26 h25 h37 h39
      (by rw [h40, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk2 (Nat.zero_le _) (by omega)
      (by rw [hax, Nat.sub_zero])
      (fun i hi => ⟨⟨s.gpr .rdx, lk.G.len⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside hp.dOdg hp.ddgs hp.dKdg (a := s.gpr .rdx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hw] at this)
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hw] at this)))
    fun u1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, hV1⟩, f1⟩ => ?_)
  have hM1 := frame_keep hp hw L.rsp hM f1
  have hw1 : u1.wr = frR s :: s.wr := wr1.trans hw
  have g : ∀ j, j < nW → (j < 23 ∨ 32 < j) → W1 j = W j := fun j hj h => hW1 j hj h
  -- The copy.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyOut]) (by exact Nat.zero_le 8)
    (copyOut_ok hp L1 R1 hw1 (by rw [g 16 (by decide) (by decide), h16]) (by rw [g 17 (by decide) (by decide), h17])
      (by omega))) fun u2 ⟨⟨L2, k2, R2, hb2, ho2⟩, f2⟩ => ?_)
  -- 1.
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = u2.mem ∧ t'.gpr .rax = 1) (by xrun) rfl)
    fun t ⟨⟨hm, hax'⟩, k⟩ => ?_
  have R' : Rep t.mem (fb s) (stackArg s 0) V1 W1 := hm ▸ R2
  refine ⟨L2.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans (k2.2.2.trans hw1),
    fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∉ [Reg.rax] ∧ r ∉ [Reg.rsi, .rdi, .r10, .rax, .r8] ∧ r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k.gpr hr'.1, k2.gpr hr'.2.1, cs1 r hr'.2.2, hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), g 41 (by decide) (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), g 42 (by decide) (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), g 43 (by decide) (by decide), h43]
  -- The outcome.
  have hdgB : (List.range H.D).map (bytesF u.mem (s.gpr .rdx)) = Spec.Rsa.bytesAt s.mem (s.gpr .rdx) lk.G.len := by
    rw [← hD]; exact bytesF_eq hM dg (by omega)
  have hsaB : (List.range (s.gpr .r8).toNat).map (bytesF u.mem (s.gpr .rcx)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat := bytesF_eq hM sa (by omega)
  rw [hdgB, hsaB] at hV1
  have hel := hp.hel
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  have he := RsaPss.encode_eq lk.G hG (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) lk.G.len)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (emBits := (s.gpr .r9).toNat)
    (by simp [Spec.Rsa.bytesAt]) hel.symm rfl (by rw [hsl, ← hD]; omega)
  simp only [OutOk, encOut, he, hsl]
  refine ⟨by rw [hax']; rfl, ?_⟩
  rw [hm, hb2]
  refine List.map_congr_left fun i hi => ?_
  rw [hV1 i (List.mem_range.mp hi), hD, Nat.sub_zero]

include hH K in
theorem encBody_safe : (encBody H).allInstrs safeI = true := by
  simp only [encBody, encMain, encPrologue, maskBits, fitH, ret0, saltFits, copyOut, seqs, Code.allInstrs,
    signEnc_safe hH K, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem encBody_xd : (encBody H).x86_64Depth = 8 := by
  simp only [encBody, encMain, ret0, copyOut, seqs, Code.x86_64Depth, signEnc_xd K, byteLoop]
  rfl

include hH K in
theorem enc_spAll : (encode H).allInstrs (fun i => !isa.writesSp i) = true := by
  have he := encBody_safe hH K
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  simp only [encode, Code.allInstrs, he.1]
  rfl

include K in
theorem enc_xd : (encode H).x86_64Depth ≤ encStack := by
  simp only [encode, Code.x86_64Depth, encBody_xd K, X86_64.Instr.frameBytes]
  unfold encStack frameBytes
  decide

/-- The epilogue: the callee-saved registers restored and the outcome. -/
theorem restore_ok {s t : State} (D : EDone G s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (encK G).post s (freedF t') := by
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
  · have hax : (freedF t').gpr .rax = t.gpr .rax := by
      show (if Reg.rax = Reg.rsp then t'.gpr .rsp + BitVec.ofNat 64 frameBytes else t'.gpr .rax) = _
      rw [ifn (by decide), k.gpr (by decide)]
    have hmem : (freedF t').mem = t.mem := hm
    have hout := D.out
    simp only [OutOk, encOut] at hout
    simp only [encK, hax, hmem]
    exact hout

include hH K in
theorem enc_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {s : State} (h : (encK lk.G).pre s) :
    WP isa (encode H) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (encK lk.G).post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := Pre.of lk.G h
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl : lk.G.len = H.D := lk.len
  refine wp_frame (by have := hp.sp1; unfold encStack frameBytes at *; omega) ?_
  refine WP.mono_mx (safe_mx (encBody_safe hH K)) (Q := fun s₂ => s₂.gpr .rsp = fb s ∧
    s₂.wr = (allocState frameBytes s).wr ∧ (∀ r ∈ calleeSaved, (freedF s₂).gpr r = s.gpr r) ∧
      (encK lk.G).post s (freedF s₂)) ?_ fun t ⟨a, b, c, d⟩ hmx =>
    ⟨a, b, c, d, by rw [show (freedF t).mxcsr = t.mxcsr from rfl, hmx]; rfl⟩
  rw [encBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  refine WP.mono (fitH_ok (H := H) (by omega) L1 R1 (k := (s.gpr .rsi).toNat)
    (by simp only [proW', proW, upd, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega)) fun t2 ⟨k2, hm2, hax2, hc2⟩ => ?_
  have L2 : Lay t2 (fb s) (stackArg s 0) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 0) _ (proW' s) := hm2 ▸ R1
  have hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rax] ∧ r ∉ [Reg.rax, .rcx] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this.1, k1.gpr this.2]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := EDone lk.G s) ?_ fun t3 D => restore_ok D)
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hel := hp.hel
  refine WP.ite (M := isa) _ (show isa.eval .b t2 = _ from hc2) (fun hb => ?_) (fun hb => ?_)
  · -- `emLen < hLen + 2`.
    rw [decide_eq_true_eq] at hb
    refine ret0_done L2 R2 hw2 hcs2 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none _ (by rw [hsl, ← hel, hGl]; omega))
  rw [decide_eq_false_iff_not] at hb
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .r8 ∧ t.mem = t2.mem) (by
    xrun [ea_sp, L2.rsp, L2.ld (d := sSaltLen) (by decide), R2.rd (d := sSaltLen) 40 rfl (by decide)]
    simp [proW', proW, upd]) rfl) fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ => ?_
  refine WP.mono (saltFits_ok (H := H) (by omega) t5 (a := (s.gpr .rsi).toNat) (b := s.gpr .r8)
    (by omega) (by omega) (by rw [k5.gpr (by decide)]; exact hax2) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ => ?_
  have L6 : Lay t6 (fb s) (stackArg s 0) := L2.congr ((k6.gpr (by decide)).trans (k5.gpr (by decide)))
    (k6.2.2.trans k5.2.2) (by rw [hm6, hm5])
  have hm62 : t6.mem = t2.mem := by rw [hm6, hm5]
  have R6 := hm62 ▸ R2
  have hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw2)
  have hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans hrd2)
  have hcs6 : ∀ r ∈ [Reg.r13, .r14, .r15], t6.gpr r = s.gpr r := fun r hr => by
    rw [k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  refine WP.ite (M := isa) _ (show isa.eval .b t6 = _ from hc6) (fun hb6 => ?_) (fun hb6 => ?_)
  · -- The salt does not fit.
    rw [decide_eq_true_eq] at hb6
    refine ret0_done L6 R6 hw6 hcs6 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none _ (by rw [hsl, ← hel, hGl]; omega))
  rw [decide_eq_false_iff_not] at hb6
  refine encMain_ok hH K lk hp L6 R6 hw6 hrd6 hcs6 (hm62 ▸ hM2)
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp only [proW', upd]; simp; rw [hel])
    (by simp [proW', upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by omega) hax6

include hH K in
/-- `encode` meets `encK`, keeping the callee-saved registers, its return
address and MXCSR's control bits. -/
theorem enc_correct (lk : Pbkdf2.Md.X86_64.MgfLink H hH) (s : State) (h : (encK lk.G).pre s) :
    ∃ t s', Exec isa (encode H) s t s' ∧ abiPreserved s s' ∧ (encK lk.G).post s s' := by
  have hp := Pre.of lk.G h
  have hsp : SpSafe (encode H) := by
    have h' := enc_spAll hH K
    rw [Code.allInstrs_eq] at h'
    intro i hi
    simpa using List.all_eq_true.mp h' i hi
  have hW := X86_64.WP.stackFrame hsp (by have := enc_xd K (H := H); unfold encStack at this; omega)
    (enc_ok hH K lk h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  have hd := enc_xd K (H := H)
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (encode H).x86_64Depth) (k := 8)
      (by unfold encStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Enc
