import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCtx
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncLoops
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `D = I2OSP(d, k)`

The private-key operation's result to its slot (`p1_step`, which starts
`Ctx`), `k` zeros at `scratch + sD` (`zeroLoop_ok`), then `d` at their end
(`copyLoop_ok`): `D`, `d` after `k - d_len` zeros, is `I2OSP(d, k)`
(`dBuild_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- The length of `d`. -/
abbrev dlOf (s : State) : Nat := (stackArg s 2).toNat

/-- After the result's store: `Ctx`, and the zero loop's registers. -/
structure P1 (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  rdi : t.gpr .rdi = sc s
  rcx : t.gpr .rcx = s.gpr .r8
  r10 : t.gpr .r10 = BitVec.ofNat 64 0
  rax : t.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32)

theorem p1_step {s t : State} (hp : DPre s) (h : PostPriv s t)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) :
    WP isa (.block dPtrs₁) t (P1 s (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s))) := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hk2 := hp.k2
  have hsi := hp.hsi
  refine WP.mono (WP.keep [.rdi, .rcx, .r10, .rax] (c := .block dPtrs₁) (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) oR) (t.gpr .rax) ∧ t'.gpr .rdi = sc s ∧ t'.gpr .rcx = s.gpr .r8 ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32)) (by
    xrun [dPtrs₁, ea_sp, h.rsp, hs.st (d := oR) (by decide), hs.ld (d := oScr) (by decide),
      hs.ld (d := oK) (by decide), word_ww _ _ _ (show oScr + 8 ≤ oR ∨ oR + 8 ≤ oScr by decide)
        (by decide) (by decide),
      word_ww _ _ _ (show oK + 8 ≤ oR ∨ oR + 8 ≤ oK by decide) (by decide) (by decide), h.slots.sScr, h.slots.sK]
    done) rfl) fun t' ⟨⟨hm, hdi, hcx, h10, hax⟩, k⟩ => ?_
  have hfw : Frame [⟨off (fb s) oR, 8⟩] t.mem t'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have w : ∀ {d : Nat}, d + 8 ≤ oR → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd => by
    rw [hm]; exact word_ww _ _ _ (.inl hd) (by unfold frameBytes at hF; unfold oR at hd; omega)
      (by unfold frameBytes at hF; unfold oR; omega)
  refine ⟨⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd, k.2.2.trans h.wr,
    frame_call h.mem hfw fun r hr => ?_,
    ⟨(w (by decide)).trans h.slots.sOut, (w (by decide)).trans h.slots.sML, (w (by decide)).trans h.slots.sN,
      (w (by decide)).trans h.slots.sK, (w (by decide)).trans h.slots.sE, (w (by decide)).trans h.slots.sEl,
      (w (by decide)).trans h.slots.sD, (w (by decide)).trans h.slots.sDl, (w (by decide)).trans h.slots.sIn,
      (w (by decide)).trans h.slots.sScr⟩, by rw [hm]; exact word_writeW_self _ _ _ _, ?_,
    fun r hr hr' => (k.cs (by decide) r hr).trans (hcs r hr hr')⟩, hdi, hcx, h10, hax⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨stkR s, by simp, frame_sub s (by decide)⟩
  · refine bytes_keep hfw (fun r hr => ?_) (by unfold kOf; omega)
    rw [List.mem_singleton.mp hr]
    have := hp.dKo; rw [hsi] at this
    exact (this.sub_left (frame_sub s (by decide))).symm

/-! ## The zeros -/

/-- After `j` zeros, from the state `t₀` before the loop. -/
structure ZInv (s t₀ : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.r10] t₀ t
  out : Outside (sc s) sD j t₀.mem t.mem
  zs : ∀ i < j, byte t.mem (sc s) (sD + i) = 0
  r10 : t.gpr .r10 = BitVec.ofNat 64 j

theorem zeroLoop_ok {s t₀ : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h : P1 s R EM t₀) :
    WP isa zeroLoop t₀ (ZInv s t₀ (kOf s)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hs := h.ctx.scr hp
  have ⟨_, hS⟩ := scr_len hp
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (kOf s) := by rw [h.rcx]; simp
  refine wp_upto (a := 0) (N := kOf s) (by unfold kOf; omega) (ZInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), h.r10⟩
  intro j _ hj u hI
  have hdi : u.gpr .rdi = sc s := (hI.keep.gpr (by decide)).trans h.rdi
  have hcx : u.gpr .rcx = BitVec.ofNat 64 (kOf s) := (hI.keep.gpr (by decide)).trans hcx'
  have hax : u.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32) := (hI.keep.gpr (by decide)).trans h.rax
  have hst : InRegions u.wr (off (sc s) (sD + j)) 1 :=
    (hs.congr hI.keep.2.2).st8 (by unfold scrBytes sD; unfold kOf at hj; omega)
  have hea : u.ea (bx .rdi .r10 sD) = off (sc s) (sD + j) := ea_bxd sD hdi hI.r10
  have hkk : kOf s ≤ 1024 := hk2
  refine WP.mono (WP.keep [.r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (sc s) (sD + j)) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = kOf s))) (by
    xrun [zeroLoop, hea, hst, hI.r10, hcx, hax, zero_trunc, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show kOf s < 2 ^ 64 by omega)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega)
      (by unfold sD; unfold kOf at hj; omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by unfold sD; unfold kOf at hj; omega)
        (by unfold sD; unfold kOf at hj; omega)]
      exact hI.zs i hi
    · exact byte_wb_self _ _ _ _


/-! ## `d` -/

/-- A byte of a buffer apart from `L` bytes at `p` lies `L` or more past `p`. -/
theorem ofs_of_disjoint {p q : Addr} {L n j : Nat} (hd : (⟨p, L⟩ : Region).Disjoint ⟨q, n⟩) (hj : j < n)
    (hn : n ≤ 2 ^ 64) : L ≤ ofs p (q + BitVec.ofNat 64 j) := by
  refine Nat.le_of_not_lt fun hl => hd (q + BitVec.ofNat 64 j) ?_ (Offset.contains_base q (by omega) (by omega))
  simp only [Region.Contains, ofs] at hl ⊢; omega

/-- A byte of a buffer the function only reads, in a state of `Ctx` and
then changed only in `scratch`. -/
theorem ctx_byte {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {m : Mem} {o n : Nat} (ho : Outside (sc s) o n t.mem m) (hon : o + n ≤ scrBytes) {q : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨q, len⟩) (hO : (outR s).Disjoint ⟨q, len⟩) (hM : (mlR s).Disjoint ⟨q, len⟩)
    (hS : (scrR s).Disjoint ⟨q, len⟩) (hl : len ≤ 2 ^ 64) {j : Nat} (hj : j < len) :
    m (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) := by
  obtain ⟨h1, _⟩ := scr_len hp
  rw [ho _ (.inr (by have := ofs_of_disjoint (p := sc s) hS hj hl; omega))]
  exact hc.mem.bytes (R := ⟨q, len⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hk.symm
    · exact hO.symm
    · exact hM.symm
    · exact hS.symm) hl hj

/-- `x + y - z` for `z ≤ y`. -/
theorem add_sub_ofNat (x : Addr) {y z : BitVec 64} (h : z.toNat ≤ y.toNat) :
    x + y - z = off x (y.toNat - z.toNat) := by
  rw [off, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := y.isLt; have := z.isLt
  omega

/-- The copy loop's registers. -/
structure P2 (s : State) (R : BitVec 64) (EM : List Byte) (t₀ t : State) : Prop where
  ctx : Ctx s R EM t
  out : Outside (sc s) sD (kOf s) t₀.mem t.mem
  zs : ∀ i < kOf s, byte t.mem (sc s) (sD + i) = 0
  rsi : t.gpr .rsi = stackArg s 1
  rcx : t.gpr .rcx = stackArg s 2
  rdi : t.gpr .rdi = off (sc s) (kOf s - dlOf s)
  r10 : t.gpr .r10 = BitVec.ofNat 64 0

theorem p2_step {s t₀ t : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h₀ : P1 s R EM t₀)
    (h : ZInv s t₀ (kOf s) t) : WP isa (.block dPtrs₂) t (P2 s R EM t₀) := by
  have hF := fb_toNat hp
  have hc₁ : Ctx s R EM t := h₀.ctx.step hp h.keep.2.1 h.keep.2.2 (h.keep.cs (by decide))
    (frame_of_out h.out (by unfold sD; have := hp.k2; unfold kOf; omega)) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by unfold sD scrBytes; have := hp.k2; unfold kOf; omega))
  have hs := hc₁.frm hp
  have hsp := hc₁.rsp
  have hdl := hp.dl2
  refine WP.mono (WP.keep [.rsi, .rcx, .rdi, .r10] (c := .block dPtrs₂) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rsi = stackArg s 1 ∧ t'.gpr .rcx = stackArg s 2 ∧
      t'.gpr .rdi = sc s + s.gpr .r8 - stackArg s 2 ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [dPtrs₂, ea_sp, hsp, hs.ld (d := oD) (by decide), hs.ld (d := oDl) (by decide),
      hs.ld (d := oScr) (by decide), hs.ld (d := oK) (by decide), hc₁.slots.sD, hc₁.slots.sDl,
      hc₁.slots.sScr, hc₁.slots.sK]) rfl) fun t' ⟨⟨hm, hsi, hcx, hdi, h10⟩, k⟩ => ?_
  have hc : Ctx s R EM t' := hc₁.step hp k.2.1 k.2.2 (k.cs (by decide)) (ws := [])
    (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨hc, by rw [hm]; exact h.out, fun i hi => by rw [hm]; exact h.zs i hi, hsi, hcx, ?_, h10⟩
  rw [hdi, add_sub_ofNat _ hdl]


/-- After `j` bytes of `d`, from the state `t₀` before the loop. -/
structure CInv (s t₀ : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  out : Outside (sc s) (sD + (kOf s - dlOf s)) j t₀.mem t.mem
  ds : ∀ i < j, byte t.mem (sc s) (sD + (kOf s - dlOf s) + i) = s.mem (stackArg s 1 + BitVec.ofNat 64 i)
  r10 : t.gpr .r10 = BitVec.ofNat 64 j

theorem copyLoop_ok {s t₁ t₀ : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h : P2 s R EM t₁ t₀) :
    WP isa copyLoop t₀ (CInv s t₀ (dlOf s)) := by
  have hk2 := hp.k2
  have hdl1 := hp.dl1
  have hdl := hp.dl2
  have hkk : kOf s ≤ 1024 := hk2
  have hd1 : 1 ≤ dlOf s := hdl1
  have hd2 : dlOf s ≤ kOf s := hdl
  have hs := h.ctx.scr hp
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (dlOf s) := by rw [h.rcx]; simp
  refine wp_upto (a := 0) (N := dlOf s) (by omega) (CInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), h.r10⟩
  intro j _ hj u hI
  have hdi : u.gpr .rdi = off (sc s) (kOf s - dlOf s) := (hI.keep.gpr (by decide)).trans h.rdi
  have hsi : u.gpr .rsi = stackArg s 1 := (hI.keep.gpr (by decide)).trans h.rsi
  have hcx : u.gpr .rcx = BitVec.ofNat 64 (dlOf s) := (hI.keep.gpr (by decide)).trans hcx'
  have hea₁ : u.ea (bx .rsi .r10) = off (stackArg s 1) (0 + j) := ea_bxd 0 hsi hI.r10
  have hea₂ : u.ea (bx .rdi .r10 sD) = off (sc s) (sD + (kOf s - dlOf s) + j) := by
    rw [ea_bxd sD hdi hI.r10, off_off, show kOf s - dlOf s + (sD + j) = sD + (kOf s - dlOf s) + j by omega]
  have hst : InRegions u.wr (off (sc s) (sD + (kOf s - dlOf s) + j)) 1 :=
    (hs.congr hI.keep.2.2).st8 (by unfold scrBytes sD; omega)
  have hjd : j < (stackArg s 2).toNat := hj
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 1) (0 + j)) 1 :=
    ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (by
      rw [hI.keep.2.1, h.ctx.rd, hp.hrd]; simp),
      by rw [Nat.zero_add]; exact Offset.contains_base _ (by omega) (by have := hp.wD; omega)⟩
  have hb : u.mem (off (stackArg s 1) (0 + j)) = s.mem (stackArg s 1 + BitVec.ofNat 64 j) := by
    rw [Nat.zero_add]
    exact ctx_byte hp h.ctx hI.out (by unfold scrBytes sD; omega) hp.dKd hp.dOd hp.dMd hp.dds.symm
      (by have := hp.wD; omega) hj
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (sc s) (sD + (kOf s - dlOf s) + j)) (s.mem (stackArg s 1 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = dlOf s))) (by
    have hidx : kOf s - dlOf s + (sD + j) = sD + (kOf s - dlOf s) + j := by omega
    xrun [copyLoop, hea₁, ea_bxd (j := j) (p := off (sc s) (kOf s - dlOf s)), hdi, off_off, hidx, hin, hst, hb, hI.r10, hcx, trunc_zext, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show dlOf s < 2 ^ 64 by omega)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega)
      (by unfold sD; omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by unfold sD; omega) (by unfold sD; omega)]
      exact hI.ds i hi
    · exact byte_wb_self _ _ _ _

/-- After `dBuild`: `D = I2OSP(d, k)` at `scratch + sD`. -/
structure DB (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  D : Spec.Rsa.bytesAt t.mem (scA s sD) (kOf s) = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s)

theorem dBuild_step {s t : State} (hp : DPre s) (h : PostPriv s t)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) :
    WP isa dBuild t (DB s (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s))) := by
  have hk2 := hp.k2
  have hdl1 := hp.dl1
  have hdl := hp.dl2
  have hkk : kOf s ≤ 1024 := hk2
  have hd1 : 1 ≤ dlOf s := hdl1
  have hd2 : dlOf s ≤ kOf s := hdl
  have hdd : dlOf s = (stackArg s 2).toNat := rfl
  refine WP.seq (WP.mono (p1_step hp h hcs) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (p2_step hp h₁ h₂) fun t₃ h₃ => ?_)
  refine WP.mono (copyLoop_ok hp h₃) fun t₄ h₄ => ?_
  have hc : Ctx s _ _ t₄ := h₃.ctx.step hp h₄.keep.2.1 h₄.keep.2.2 (h₄.keep.cs (by decide))
    (frame_of_out h₄.out (by unfold sD; omega)) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by unfold sD scrBytes; omega))
  refine ⟨hc, ?_⟩
  rw [i2osp_os2ip_pad _ (by rw [blen]; exact hdl), blen]
  refine List.ext_getElem (by simp only [blen, List.length_append, List.length_replicate]; omega)
    fun i h₁ h₂ => ?_
  rw [bget, off_add]
  simp only [blen] at h₁
  by_cases hi : i < kOf s - dlOf s
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate,
      h₄.out _ (.inl (by rw [ofs_off0 _ (by unfold sD; omega)]; omega))]
    exact h₃.zs i h₁
  · rw [List.getElem_append_right (by simp; omega), bget]
    simp only [List.length_replicate]
    have := h₄.ds (i - (kOf s - dlOf s)) (by omega)
    rw [show sD + (kOf s - dlOf s) + (i - (kOf s - dlOf s)) = sD + i by omega] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
