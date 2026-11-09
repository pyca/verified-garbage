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
import VerifiedGarbage.Proof.Framework.X86_64.Syms

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

variable {T : Tabs}

/-- What `encK.post` asks for: the encoding with the hash function `Hs` (of
digests of `D` bytes) and MGF1's `Gs`. -/
def encOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (s.gpr .r9).toNat

/-- The outcome, from the memory and `rax`. -/
def OutOk (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) (m : Mem) (rax : BitVec 64) : Prop :=
  match encOut D Hs Gs s with
  | some e => rax.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = e
  | none => rax.setWidth 32 = 0

/-- Before the epilogue: the outcome, the saved registers in their slots. -/
structure EDone (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : OutOk D Hs Gs s t.mem (t.gpr .rax)

/-- A refusal: 0. -/
theorem ret0_done {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 0)) (R : Rep t.mem (fb s) (stackArg s 0) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hn : encOut D Hs Gs s = none) :
    WP isa ret0 t (EDone D Hs Gs s) := by
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

variable (hH : Pbkdf2.Md.X86_64.HashOK T.H) (K : Pbkdf2.Md.X86_64.Callees T.H)
  (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
  (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) (hf : MdFnsSafe T.f) (hg : FnsSafe T.g) (hdk : DigOK T.H)

/-- The copy of `EM` to `em`. -/
theorem copyOut_ok {s u : State} (hp : Pre T s) {V : Nat → Byte} {W : Nat → BitVec 64}
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

include hH K hG hGh hGl hGv hf hg hdk in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) {s u : State} (hp : Pre T s) {V : Nat → Byte}
    {W : Nat → BitVec 64} (L : Lay u (fb s) (stackArg s 0)) (R : Rep u.mem (fb s) (stackArg s 0) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r)
    (hM : Frame (wrR s) s.mem u.mem) (hT : HT T.H T.dn T.f W u.syms) (hGT : GT T.G T.g W u.syms)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rsi)
    (h25 : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat)))
    (h26 : W 26 = 0) (h37 : W 37 = s.gpr .rdx) (h39 : W 39 = s.gpr .rcx) (h40 : W 40 = s.gpr .r8)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12)
    (hfit : T.H.D + (s.gpr .r8).toNat + 2 ≤ (s.gpr .rsi).toNat)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - (T.H.D + 2))) :
    WP isa (encMain T.f T.H T.g) u (EDone T.H.D lk.G Gs s) := by
  have hk2 := hp.k2
  have hD : T.H.D = lk.G.len := lk.len.symm
  have hHv := validG hH lk.hash lk.len
  have dg : ∀ r ∈ wrR s, (⟨s.gpr .rdx, T.H.D⟩ : Region).Disjoint r := in_apart hp.dKdg hp.dOdg hp.ddgs
  have sa : ∀ r ∈ wrR s, (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint r :=
    in_apart hp.dKsa hp.dOsa hp.dsas
  have hdg : (s.gpr .rdx).toNat + T.H.D ≤ 2 ^ 64 := hp.wDg
  have hsa := hp.wSa
  rw [encMain]
  simp only [seqs]
  -- The encoding.
  refine WP.seq (WP.mono (WP.keepIn (signEnc_safe hH hf hg) (signEnc_xd hf hg)
    (signEnc_ok hH K lk hG hGh hGl hGv hf hdk L R hT hGT (k := (s.gpr .rsi).toNat) (lo := 0)
      (sl := (s.gpr .r8).toNat) (c := (0xFF : Byte) >>> (8 * (s.gpr .rsi).toNat - (s.gpr .r9).toNat))
      (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h26 h25 h37 h39
      (by rw [h40, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk2 (Nat.zero_le _) (by omega)
      (by rw [hax, Nat.sub_zero])
      (fun i hi => ⟨⟨s.gpr .rdx, T.H.D⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
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
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyOut]) (by exact Nat.zero_le 16)
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
  have hdgB : (List.range T.H.D).map (bytesF u.mem (s.gpr .rdx)) = Spec.Rsa.bytesAt s.mem (s.gpr .rdx) T.H.D :=
    bytesF_eq hM dg (by omega)
  have hsaB : (List.range (s.gpr .r8).toNat).map (bytesF u.mem (s.gpr .rcx)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat := bytesF_eq hM sa (by omega)
  rw [hdgB, hsaB] at hV1
  have hel := hp.hel
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  have he := RsaPss.encode_eq₂ lk.G Gs hHv hGv (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) T.H.D)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (emBits := (s.gpr .r9).toNat)
    (by simp [Spec.Rsa.bytesAt, hD]) hel.symm rfl (by rw [hsl, ← hD]; omega)
  simp only [OutOk, encOut, he, hsl]
  refine ⟨by rw [hax']; rfl, ?_⟩
  rw [hm, hb2]
  refine List.map_congr_left fun i hi => ?_
  rw [hV1 i (List.mem_range.mp hi), hD, Nat.sub_zero]

include hH hf hg in
theorem encBody_safe : (encBody T.f T.H T.g).allInstrs safeI = true := by
  simp only [encBody, encMain, encPrologue, maskBits, fitH, ret0, saltFits, copyOut, hSlots, gSlots, seqs,
    Code.allInstrs, signEnc_safe hH hf hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf hg in
theorem encBody_xd : (encBody T.f T.H T.g).x86_64Depth ≤ 16 := by
  have := signEnc_xd (H := T.H) hf hg
  simp only [encBody, encMain, ret0, copyOut, seqs, Code.x86_64Depth, byteLoop, Nat.max_le]
  omega

include hH hf hg in
theorem enc_spAll : (encode T.f T.H T.g).allInstrs (fun i => !isa.writesSp i) = true := by
  have he := encBody_safe hH hf hg
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  simp only [encode, Code.allInstrs, he.1]
  rfl

include hf hg in
theorem enc_xd : (encode T.f T.H T.g).x86_64Depth ≤ encStack := by
  have := encBody_xd (T := T) hf hg
  simp only [encode, Code.x86_64Depth, X86_64.Instr.frameBytes]
  unfold encStack frameBytes at *
  omega

/-- The epilogue: the callee-saved registers restored and the outcome. -/
theorem restore_ok {Hs : Spec.Mgf1.Hash} {s t : State} (D : EDone T.H.D Hs Gs s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (encK T Hs Gs).post s (freedF t') := by
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

include hH K hG hGh hGl hGv hf hg hdk in
theorem enc_ok (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) {s : State} (h : (encK T lk.G Gs).pre s) :
    WP isa (encode T.f T.H T.g) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (encK T lk.G Gs).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := Pre.of T h
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGl' : lk.G.len = T.H.D := lk.len
  refine wp_frame (by have := hp.sp1; unfold encStack frameBytes at *; omega) ?_
  refine WP.mono_mx (safe_mx (encBody_safe hH hf hg)) (Q := fun s₂ => s₂.gpr .rsp = fb s ∧
    s₂.wr = (allocState frameBytes s).wr ∧ (∀ r ∈ calleeSaved, (freedF s₂).gpr r = s.gpr r) ∧
      (encK T lk.G Gs).post s (freedF s₂)) ?_ fun t ⟨a, b, c, d⟩ hmx =>
    ⟨a, b, c, d, by rw [show (freedF t).mxcsr = t.mxcsr from rfl, hmx]; rfl⟩
  rw [encBody]
  simp only [seqs]
  -- The prologue, and the tables' words to their slots.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ s1 => ?_
  refine X86_64.WP.mono_syms (argR11_ok hp L1.rsp k1.2.1 f1 (j := 2) (by decide)) fun t1' ⟨k1', hm1', h11⟩ s1' => ?_
  have L1' : Lay t1' (fb s) (stackArg s 0) := L1.congr (k1'.gpr (by decide)) k1'.2.2 (by rw [hm1'])
  refine WP.seq (X86_64.WP.mono_syms (hSl_ok hp L1' (hm1' ▸ R1) (k1'.2.1.trans k1.2.1) (hm1' ▸ f1) h11)
    fun t2 ⟨k2, L2, h2, f2, R2⟩ s2 => ?_)
  have hrd2 : t2.rd = s.rd := k2.2.1.trans (k1'.2.1.trans k1.2.1)
  refine WP.seq (X86_64.WP.mono_syms (gSl_ok hp L2 R2 hrd2 f2 h2) fun t3 ⟨k3, L3, f3, R3⟩ s3 => ?_)
  have sy3 : t3.syms = s.syms := s3.trans (s2.trans (s1'.trans s1))
  refine WP.seq (X86_64.WP.mono_syms (fitH_ok (H := T.H) (by omega) L3 R3 (k := (s.gpr .rsi).toNat)
    (by simp only [proW', proW, upd, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega)) fun t4 ⟨k4, hm4, hax4, hc4⟩ s4 => ?_)
  have L4 : Lay t4 (fb s) (stackArg s 0) := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 := hm4 ▸ R3
  have hM4 : Frame (wrR s) s.mem t4.mem := hm4 ▸ frame_wrR f3
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans (k3.2.2.trans (k2.2.2.trans (k1'.2.2.trans k1.2.2)))
  have hrd4 : t4.rd = s.rd := k4.2.1.trans (k3.2.1.trans hrd2)
  have hcs4 : ∀ r ∈ [Reg.r13, .r14, .r15], t4.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rax] ∧ r ∉ [Reg.rax, .rcx] ∧ r ∉ [Reg.rax, .r11] ∧ r ∉ [Reg.r11] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k4.gpr this.1, k3.gpr this.1, k2.gpr this.2.2.1, k1'.gpr this.2.2.2, k1.gpr this.2.1]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  have sy4 : t4.syms = s.syms := s4.trans sy3
  refine WP.seq (WP.mono (Q := EDone T.H.D lk.G Gs s) ?_ fun t3 D => restore_ok D)
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .r8).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hel := hp.hel
  refine WP.ite (M := isa) _ (show isa.eval .b t4 = _ from hc4) (fun hb => ?_) (fun hb => ?_)
  · -- `emLen < hLen + 2`.
    rw [decide_eq_true_eq] at hb
    refine ret0_done L4 R4 hw4 hcs4 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none₂ _ _ (by rw [hsl, ← hel, hGl']; omega))
  rw [decide_eq_false_iff_not] at hb
  -- The salt fits.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .r8 ∧ t.mem = t4.mem) (by
    xrun [ea_sp, L4.rsp, L4.ld (d := sSaltLen) (by decide), R4.rd (d := sSaltLen) 40 rfl (by decide)]
    simp [proW', proW, upd]) rfl) fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ s5 => ?_
  refine X86_64.WP.mono_syms (saltFits_ok (H := T.H) (by omega) t5 (a := (s.gpr .rsi).toNat) (b := s.gpr .r8)
    (by omega) (by omega) (by rw [k5.gpr (by decide)]; exact hax4) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ s6 => ?_
  have L6 : Lay t6 (fb s) (stackArg s 0) := L4.congr ((k6.gpr (by decide)).trans (k5.gpr (by decide)))
    (k6.2.2.trans k5.2.2) (by rw [hm6, hm5])
  have hm64 : t6.mem = t4.mem := by rw [hm6, hm5]
  have R6 := hm64 ▸ R4
  have hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw4)
  have hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans hrd4)
  have hcs6 : ∀ r ∈ [Reg.r13, .r14, .r15], t6.gpr r = s.gpr r := fun r hr => by
    rw [k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k5.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs4 r hr]
  have sy6 : t6.syms = s.syms := s6.trans (s5.trans sy4)
  refine WP.ite (M := isa) _ (show isa.eval .b t6 = _ from hc6) (fun hb6 => ?_) (fun hb6 => ?_)
  · -- The salt does not fit.
    rw [decide_eq_true_eq] at hb6
    refine ret0_done L6 R6 hw6 hcs6 (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
      (by simp [proW', proW, upd]) (RsaPss.encode_none₂ _ _ (by rw [hsl, ← hel, hGl']; omega))
  rw [decide_eq_false_iff_not] at hb6
  have tb := hp.tabs
  refine encMain_ok hH K hG hGh hGl hGv hf hg hdk lk hp L6 R6 hw6 hrd6 hcs6 (hm64 ▸ hM4) ?_ ?_
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp only [proW', upd]; simp; rw [hel])
    (by simp [proW', upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd])
    (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by simp [proW', proW, upd]) (by omega) hax6
  · rw [sy6]; exact tb.hf.ht (by simpa [upd] using tb.h0) (by simpa [upd] using tb.h3) (by simpa [upd] using tb.h4)
  · rw [sy6]
    exact tb.gf.gt (by simpa [upd] using tb.g0) (by simpa [upd] using tb.g1) (by simpa [upd] using tb.g2) (by simpa [upd] using tb.g4)

include hH K hG hGh hGl hGv hf hg hdk in
/-- `encode` meets `encK`, keeping the callee-saved registers, its return
address and MXCSR's control bits. -/
theorem enc_correct (lk : Pbkdf2.Md.X86_64.MgfLink T.H hH) (s : State) (h : (encK T lk.G Gs).pre s) :
    ∃ t s', Exec isa (encode T.f T.H T.g) s t s' ∧ abiPreserved s s' ∧ (encK T lk.G Gs).post s s' := by
  have hp := Pre.of T h
  have hsp : SpSafe (encode T.f T.H T.g) := by
    have h' := enc_spAll hH hf hg
    rw [Code.allInstrs_eq] at h'
    intro i hi
    simpa using List.all_eq_true.mp h' i hi
  have hd := enc_xd (T := T) hf hg
  have hW := X86_64.WP.stackFrame hsp (by unfold encStack at hd; omega)
    (enc_ok hH K hG hGh hGl hGv hf hg hdk lk h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf'⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  refine Mem.readW_congr fun i hi => hf' _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (encode T.f T.H T.g).x86_64Depth) (k := 8)
      (by unfold encStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Enc
