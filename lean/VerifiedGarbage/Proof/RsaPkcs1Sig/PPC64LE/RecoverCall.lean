module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverPre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the call

As `vg_rsa_pkcs1_verify_precomputed`'s (`VerifyCall.lean`): `pubArgs_ok`, the
block before the call, keeps `out`, `out_len`, `k` and `hash` in `r28`–`r31`
and sets up the call of `vg_rsa_public_precomputed_checked` (`AtCall`);
`call_ok`, the call writes RSAVP1's result to `EM₁` if `pre` holds the
modulus' values (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

/-- In the frame, `out`, `out_len`, `k` and `hash` kept. -/
abbrev RMid (s t : State) : Prop :=
  Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t

/-- At the call: the arguments of `vg_rsa_public_precomputed_checked`, `EM₁`,
`n_len`, `pre`, `pre_len`, `e`, `e_len`, `sig` and `n_len`, and on the stack
`scratch` and `scratch_len`. -/
structure AtCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t where
  g3 : t.gpr .r3 = fb s + BitVec.ofNat 64 oEM1
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 3
  g6 : t.gpr .r6 = stackArg s 4
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = s.gpr .r10
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

section
variable {s : State}

/-- The stack arguments are readable. -/
theorem arg_rd (hp : PreR s) (rs : List Region) {j : Nat} (hj : j < 5) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨aR s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_aR hj⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame (hp : PreR s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

end

theorem pubArgs_ok {s u : State} (hp : PreR s) (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.r11, .r12] → u.gpr r = s.gpr r)
    (hlr : u.lr = s.lr) :
    WP isa (.block pubArgs) u (AtCall s) := by
  unfold pubArgs
  rw [List.append_assoc]
  refine save_ok hsp hwr hm (fun r hr => hg r (by revert r; decide)) hlr fun v kv v12 fv sv lv => ?_
  have gv : ∀ r, r ∉ [Reg.r12, .r0, .r11] → v.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kv.gpr r (by simp [hr.1, hr.2.1]), hg r (by simp [hr.1, hr.2.2])]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_lsrw fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_mov fun v₈ o₈ e₈ => ?_
  have O₈ : Only [.r28, .r29, .r30, .r31, .r9, .r10, .r4] v v₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₈)))))).mono
  have r12₈ : v₈.gpr .r12 = fb s := by rw [O₈.get .r12, v12]
  have rd₈ : v₈.rd = s.rd := by rw [O₈.rd, kv.rd, hrd]
  have wr₈ : v₈.wr = fr s :: s.wr := by rw [O₈.wr, kv.wr, hwr]
  have sp₈ : v₈.sp = fb s := by rw [O₈.sp, kv.sp, hsp]
  unfold callTail
  refine wp_ld (a := stackArgAddr s 1) (by rw [r12₈, stackArgAddr_fb]) (by rw [rd₈]; exact arg_rd hp _ (by decide))
    fun v₉ o₉ e₉ => ?_
  rw [O₈.mem, arg_frame hp fv (by decide)] at e₉
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [o₉.get .r12, r12₈])
    (by rw [o₉.wr, wr₈]; exact in_fr s _ (by decide) (by decide)) fun v₁₀ m₁₀ => ?_
  have f₁₀ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] v.mem v₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, O₈.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))
  have r12₁₀ : v₁₀.gpr .r12 = fb s := by rw [m₁₀.gpr, o₉.get .r12, r12₈]
  have K₁₀ : Frame [kR s] s.mem v₁₀.mem := fv.trans (f₁₀.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  refine wp_ld (a := stackArgAddr s 2) (by rw [r12₁₀, stackArgAddr_fb])
    (by rw [m₁₀.rd, o₉.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₁ o₁₁ e₁₁ => ?_
  rw [arg_frame hp K₁₀ (by decide)] at e₁₁
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₁₁.get .r12, r12₁₀])
    (by rw [o₁₁.wr, m₁₀.wr, o₉.wr, wr₈]; exact in_fr s _ (by decide) (by decide)) fun v₁₂ m₁₂ => ?_
  have f₁₂ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] v.mem v₁₂.mem := by
    rw [m₁₂.mem, o₁₁.mem]
    exact f₁₀.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  have K₁₂ : Frame [kR s] s.mem v₁₂.mem := fv.trans (f₁₂.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  have r12₁₂ : v₁₂.gpr .r12 = fb s := by rw [m₁₂.gpr, o₁₁.get .r12, r12₁₀]
  have rd₁₂ : v₁₂.rd = s.rd := by rw [m₁₂.rd, o₁₁.rd, m₁₀.rd, o₉.rd, rd₈]
  refine wp_ld (a := stackArgAddr s 3) (by rw [r12₁₂, stackArgAddr_fb])
    (by rw [rd₁₂]; exact arg_rd hp _ (by decide)) fun v₁₃ o₁₃ e₁₃ => ?_
  refine wp_ld (a := stackArgAddr s 4) (by rw [o₁₃.get .r12, r12₁₂, stackArgAddr_fb])
    (by rw [o₁₃.rd, rd₁₂]; exact arg_rd hp _ (by decide)) fun v₁₄ o₁₄ e₁₄ => ?_
  refine wp_addi fun v₁₅ o₁₅ e₁₅ => wp_nil ?_
  rw [arg_frame hp K₁₂ (by decide)] at e₁₃
  rw [o₁₃.mem, arg_frame hp K₁₂ (by decide)] at e₁₄
  have O₁₅ : Only [.r5, .r6, .r3] v₁₂ v₁₅ := (o₁₃.trans (o₁₄.trans o₁₅)).mono
  have g₁₂ : ∀ r, r ∉ [Reg.r0] → v₁₂.gpr r = v₈.gpr r := fun r hr => by
    rw [m₁₂.gpr, o₁₁.gpr r hr, m₁₀.gpr, o₉.gpr r hr]
  have mem₁₅ : v₁₅.mem = v₁₂.mem := O₁₅.mem
  have hd : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)], ∀ {e k : Nat}, 112 ≤ e → e + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, k⟩ r := fun r hr e k h₁ h₂ => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by unfold frameBytes at h₂; omega) (by decide)
  refine {
    sp := by rw [O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈]
    rd := by rw [O₁₅.rd, rd₁₂]
    wr := by rw [O₁₅.wr, m₁₂.wr, o₁₁.wr, m₁₀.wr, o₉.wr, wr₈]
    r28 := by
      rw [O₁₅.get .r28, g₁₂ .r28 (by decide), o₈.get .r28, o₆.get .r28, o₅.get .r28, o₄.get .r28, o₃.get .r28,
        o₂.get .r28, e₁, gv .r3 (by decide)]
    r29 := by
      rw [O₁₅.get .r29, g₁₂ .r29 (by decide), o₈.get .r29, o₆.get .r29, o₅.get .r29, o₄.get .r29, o₃.get .r29,
        e₂, o₁.get .r4, gv .r4 (by decide)]
    r30 := by
      rw [O₁₅.get .r30, g₁₂ .r30 (by decide), o₈.get .r30, o₆.get .r30, o₅.get .r30, o₄.get .r30, e₃,
        o₂.get .r6, o₁.get .r6, gv .r6 (by decide)]
    r31 := by
      rw [O₁₅.get .r31, g₁₂ .r31 (by decide), o₈.get .r31, o₆.get .r31, o₅.get .r31, e₄, o₃.get .r9,
        o₂.get .r9, o₁.get .r9, gv .r9 (by decide), BitVec.ushiftRight_zero]
    hi := fun r hr => by
      have h₁ : r ∉ [Reg.r5, .r6, .r3] := by revert r; decide
      have h₂ : r ∉ [Reg.r0] := by revert r; decide
      have h₃ : r ∉ [Reg.r28, .r29, .r30, .r31, .r9, .r10, .r4] := by revert r; decide
      have h₄ : r ∉ [Reg.r12, .r0, .r11] := by revert r; decide
      rw [O₁₅.gpr r h₁, g₁₂ r h₂, O₈.gpr r h₃, gv r h₄]
    mem := by
      rw [mem₁₅]
      exact K₁₂.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₅]
      exact sv.frame_in saved_offs f₁₂ fun r hr => hd r hr (by decide) (by decide)
    ls := by
      rw [mem₁₅, f₁₂.readW (Region.contains_self _ _) (fun r hr => hd r hr (by decide) (by decide)) (by decide)]
      exact lv
    g3 := by rw [e₁₅, o₁₄.get .r12, o₁₃.get .r12, r12₁₂]
    g4 := by
      rw [O₁₅.get .r4, g₁₂ .r4 (by decide), e₈, o₆.get .r6, o₅.get .r6, o₄.get .r6, o₃.get .r6, o₂.get .r6,
        o₁.get .r6, gv .r6 (by decide)]
    g5 := by rw [o₁₅.get .r5, o₁₄.get .r5, e₁₃]
    g6 := by rw [o₁₅.get .r6, e₁₄]
    g7 := by rw [O₁₅.get .r7, g₁₂ .r7 (by decide), O₈.get .r7, gv .r7 (by decide)]
    g8 := by rw [O₁₅.get .r8, g₁₂ .r8 (by decide), O₈.get .r8, gv .r8 (by decide)]
    g9 := by
      rw [O₁₅.get .r9, g₁₂ .r9 (by decide), o₈.get .r9, o₆.get .r9, e₅, o₄.get .r10, o₃.get .r10,
        o₂.get .r10, o₁.get .r10, gv .r10 (by decide)]
    g10 := by
      rw [O₁₅.get .r10, g₁₂ .r10 (by decide), o₈.get .r10, e₆, o₅.get .r6, o₄.get .r6, o₃.get .r6,
        o₂.get .r6, o₁.get .r6, gv .r6 (by decide)]
    a0 := by
      show v₁₅.mem.readW (stackArgAddr v₁₅ 0) 64 = _
      rw [stackArgAddr_in, O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈, mem₁₅, m₁₂.mem, o₁₁.mem,
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₁₀.mem,
        Mem.readW_writeW_self64]
      exact e₉
    a1 := by
      show v₁₅.mem.readW (stackArgAddr v₁₅ 1) 64 = _
      rw [stackArgAddr_in, O₁₅.sp, m₁₂.sp, o₁₁.sp, m₁₀.sp, o₉.sp, sp₈, mem₁₅, m₁₂.mem, Mem.readW_writeW_self64,
        e₁₁] }

/-- The values of the modulus `pre` holds, which the result is about. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (s.gpr .r6).toNat)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .r6).toNat⟩

theorem em1_sub {s : State} (hp : PreR s) : Region.Sub (em1R s) (kR s) :=
  frame_sub s (by have := hp.k2; unfold oEM1 frameBytes; omega)

theorem pdOk_of {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r6) : PdOk t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp.sp1
  have hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r6).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, ha.sp]
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, ha.a1, hsa]
    exact {
      on := hp.kp.sub_left (em1_sub hp)
      oe := hp.ke.sub_left (em1_sub hp)
      oi := hgK.sub_left (em1_sub hp)
      os := hp.ks.sub_left (em1_sub hp)
      oa := Offset.disjoint _ (.inr (by decide)) (by unfold oEM1 frameBytes at *; omega) (by decide)
      ns := hp.sp.symm
      es := hp.es
      is := hgS
      sa := (hp.ks.sub_left (frame_sub s (by decide))).symm
      wo := by
        show (fb s + BitVec.ofNat 64 oEM1).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
      wn := hp.wp
      we := hp.we
      wi := by have := hp.wg; rwa [hsig] at this
      ws := hp.ws }
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    have hg : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by rw [hp.hrd, ← hsig]; simp
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (hm _ hg) (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, ha.a1, ha.wr]
    exact Covers.cons (Covers.one (in_fr s _ (by decide) (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp))
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact hp.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact hp.e1
  case he2 => rw [ha.g8, ha.g4]; exact hp.e2
  case hs => rw [ha.g4, ha.a1]; exact hp.hs

/-- After the call: `RMid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .r3) (s.gpr .r4) (s.gpr .r6) ((s.gpr .r9).setWidth 32 |>.setWidth 64) t where
  res : PreOk s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreR s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .r6) :
    WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha hsig) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1] at hf
  have hfm := ha.toMid.frameMem hp.ks (e := oEM1) (n := (s.gpr .r6).toNat) (by decide)
    (by unfold oEM1 frameBytes; omega) hf
  have hfr0 : Frame [kR s, sR s] s.mem t.mem := ha.mem
  have hgK : (kR s).Disjoint ⟨s.gpr .r10, (s.gpr .r6).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .r10, (s.gpr .r6).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  refine { ha.toMid.of (fun r hr => hpres r (by revert r; decide)) hsp' hrd' hwr' hfm.1 hfm.2.1 hfm.2.2 with
    res := fun hc => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g5, ha.g6]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, Proof.RsaPkcs1Sig.bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, bytes_of_frame hfr0 hp.ke hp.es.symm (by have := hp.we; omega),
    bytes_of_frame hfr0 hgK hgS.symm (by omega)] at this
  exact this

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
