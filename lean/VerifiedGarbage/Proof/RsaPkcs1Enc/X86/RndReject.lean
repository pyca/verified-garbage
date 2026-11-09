module

-- separate module: its proofs build in parallel with `RndAccept`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndScan
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: too few nonzero octets

With `PS` not full, the tape has fewer nonzero octets than `PS` needs: `out`
zeroed (`zeroOut_vp`), the octets drawn wiped (`drawn_vp`), and by the
budget (`budget_vp`) the status 3 with `tape = [rand_len, 0]`
(`exhausted_vp`), or 0 with `tape = [0, min(cap, rand_len + left)]`
(`request_vp`): what the function writes and returns (`reject_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : RP}

/-- `out`'s bytes zero. -/
abbrev Zout (P : RP) (m : Mem) : Prop := Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = List.replicate P.K 0

/-- `out` and the count of its bytes, to zero. -/
structure RJ1 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask P.mask.length)
  short : cnt P.mask P.mask.length < P.pl
  si : s.gpr .esi = P.out
  cx : s.gpr .ecx = BitVec.ofNat 32 P.K
  ax : s.gpr .eax = 0

/-- `out` zeroed. -/
structure RJ2 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask P.mask.length)
  short : cnt P.mask P.mask.length < P.pl
  zero : Zout P s.mem

/-- The octets drawn, to wipe. -/
structure RJ3 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask P.mask.length)
  short : cnt P.mask P.mask.length < P.pl
  zero : Zout P s.mem
  cx : s.gpr .ecx = BitVec.ofNat 32 (cnt P.mask P.mask.length)
  si : s.gpr .esi = P.B + BitVec.ofNat 32 oBuf
  ax : s.gpr .eax = 0
  zf : s.zf = some (decide (cnt P.mask P.mask.length = 0))

/-- The budget, against the tape's length. -/
structure RJ5 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask P.mask.length)
  short : cnt P.mask P.mask.length < P.pl
  zero : Zout P s.mem
  ax : s.gpr .eax = BitVec.ofNat 32 P.len
  bx : s.gpr .ebx = BitVec.ofNat 32 (P.pl + 128)
  si : s.gpr .esi = P.tape
  cf : s.cf = some (decide (P.len < P.pl + 128))

/-- The request, against the budget. -/
structure RJ6 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  short : cnt P.mask P.mask.length < P.pl
  zero : Zout P s.mem
  ax : s.gpr .eax = BitVec.ofNat 32 (P.len + (P.pl - cnt P.mask P.mask.length))
  bx : s.gpr .ebx = BitVec.ofNat 32 (P.pl + 128)
  si : s.gpr .esi = P.tape
  lt : P.len < P.pl + 128
  cf : s.cf = some (decide (P.pl + 128 < P.len + (P.pl - cnt P.mask P.mask.length)))

/-- The request. -/
structure RJ7 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  short : cnt P.mask P.mask.length < P.pl
  zero : Zout P s.mem
  ax : s.gpr .eax = BitVec.ofNat 32 (min (P.pl + 128) (P.len + (P.pl - cnt P.mask P.mask.length)))
  si : s.gpr .esi = P.tape
  lt : P.len < P.pl + 128

theorem In.k32 {σ : State} (h : In P σ) : P.K < 2 ^ 32 := by have := h.k1024; omega

theorem In.out_fit {σ : State} (h : In P σ) : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := h.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at this

theorem zeroOut_vp : VP (fun σ s => Dz P σ s ∧ isa.eval .e s = some false) (.block zeroOutArgs) (RJ1 P) ∧
    VP (RJ1 P) zeroLoop (RJ2 P) := by
  refine ⟨VP.taint [.esp] zeroOutArgs_taint (sp_agree fun _ _ h => h.1.1.hs)
    fun σ s ⟨⟨h, z⟩, he⟩ => ?_, VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.si, h₂.si]
      · rw [h₁.cx, h₂.cx]) fun σ s h => ?_⟩
  · have hc : cnt P.mask P.mask.length ≠ P.pl := by
      change s.zf = _ at he; rw [z] at he; simpa using he
    have hle := h.hs.1.cnt_le h.jN
    simp only [zeroOutArgs]
    refine h.hs.2.wp_arg (j := 0) (r := .esi) (by simp) (by decide) fun t1 s1 u1 => ?_
    refine s1.wp_arg (j := 4) (r := .ecx) (by simp) (by decide) fun t2 s2 u2 => ?_
    refine wp_movi fun t3 u3 => WP.block_nil ⟨⟨h.hs.1, s2.upd u3 (by decide)⟩, ?_, by omega, ?_, ?_, u3.gpr⟩
    · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.dx]
    · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
    · rw [u3.other _ (by decide), u2.gpr]; rfl
  · have hs := h.hs
    have hk := hs.1.k64
    have hK := hs.1.k32
    refine WP.mono (zero_ok (p := P.out) (n := P.K) (by omega) hK hs.1.out_fit h.si h.cx h.ax
      ⟨P.OUT, hs.2.inRw (by simp), Region.contains_self _ _⟩) fun t ht => ?_
    have fr : Frame [P.OUT] s.mem t.mem := by
      rw [ht.mem]
      have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.out.setWidth 64) (List.replicate P.K 0)
      simpa using this
    refine ⟨⟨hs.1, hs.2.write fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩)
      ht.rd ht.wr (ht.other _ (by decide) (by decide))⟩, by rw [ht.other _ (by decide) (by decide), h.dx],
      h.short, ?_⟩
    rw [Zout, ht.mem]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes s.mem (P.out.setWidth 64) (List.replicate P.K 0) (by simp; omega)
    simpa using this

theorem drawnArgs_vp : VP (RJ2 P) (.block drawnArgs) (RJ3 P) :=
  VP.taint [.esp, .edx] drawnArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.hs.2.sp, h₂.hs.2.sp]
      · rw [h₁.dx, h₂.dx]) fun σ s h => by
    have hpl := h.hs.1.pl1021
    have := h.short
    simp only [drawnArgs]
    refine wp_psLen h.hs (r := .ecx) (t := .eax) (by decide) (by decide) (by decide) fun t1 s1 c1 o1 m1 => ?_
    refine wp_sub fun t2 u2 _ => wp_mov fun t3 u3 => wp_addi fun t4 u4 => wp_movi fun t5 u5 => ?_
    refine wp_test fun t6 u6 z6 => WP.block_nil ?_
    have st := ((((s1.2.upd u2 (by decide)).upd u3 (by decide)).upd u4 (by decide)).upd u5 (by decide)).fupd u6
    have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
    have dx1 : t1.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask P.mask.length) := by
      rw [o1 _ (by decide) (by decide), h.dx]
    have cx5 : t5.gpr .ecx = BitVec.ofNat 32 (cnt P.mask P.mask.length) := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, c1, dx1,
        sub_ofNat (by omega)]
      congr 1; have := h.short; omega
    refine ⟨⟨h.hs.1, st⟩, ?_, h.short, by rw [Zout, mm]; exact h.zero, by rw [u6.gpr]; exact cx5, ?_, ?_, ?_⟩
    · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), dx1]
    · rw [u6.gpr, u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide), s1.2.sp]
    · rw [u6.gpr, u5.gpr]
    · rw [z6, cx5, BitVec.and_self, ofNat_beq_zero (by omega)]

theorem drawn_vp : VP (RJ3 P) (.ite .ne zeroLoop (.block [])) (RJ2 P) := by
  refine VP.ite (fun _ _ h => ⟨_, by show Option.map (!·) _ = _; rw [h.zf]; rfl⟩)
    (fun _ _ _ _ h₁ h₂ => by show eval .ne _ = eval .ne _; simp only [eval]; rw [h₁.zf, h₂.zf])
    (VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.si, h₂.1.si]
      · rw [h₁.1.cx, h₂.1.cx]) fun σ s ⟨h, he⟩ => ?_)
    (VP.block_nil fun σ s ⟨h, _⟩ => ⟨h.hs, h.dx, h.short, h.zero⟩)
  have hs := h.hs
  have ok := hs.1.ok
  have hpl := hs.1.pl1021
  have fit := hs.1.fit
  have hb := hs.1.bufA
  have hc0 : cnt P.mask P.mask.length ≠ 0 := by
    change Option.map (!·) s.zf = _ at he; rw [h.zf] at he; simpa using he
  have short := h.short
  have hF : oBuf + cnt P.mask P.mask.length ≤ P.lay.F := by
    show _ ≤ frameBytes; simp only [oBuf, frameBytes]; omega
  have hpt : (P.B + BitVec.ofNat 32 oBuf).toNat + cnt P.mask P.mask.length ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oBuf) (by decide)]
    simp only [oBuf, frameBytes] at fit ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  refine WP.mono (zero_ok (p := P.B + BitVec.ofNat 32 oBuf) (n := cnt P.mask P.mask.length) (by omega)
    (by omega) hpt h.si h.cx h.ax (by rw [hb]; exact hs.2.inFr hF)) fun t ht => ?_
  have fr : Frame [⟨P.lay.fr oBuf, cnt P.mask P.mask.length⟩] s.mem t.mem := by
    rw [ht.mem, hb]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.lay.fr oBuf) (List.replicate (cnt P.mask P.mask.length) 0)
    simpa using this
  have hd : oBuf + cnt P.mask P.mask.length ≤ P.lay.F + 16 := by
    show _ ≤ frameBytes + 16; simp only [oBuf, frameBytes]; omega
  refine ⟨⟨hs.1, hs.2.frameW hF fr ht.rd ht.wr (ht.other _ (by decide) (by decide))⟩,
    by rw [ht.other _ (by decide) (by decide), h.dx], short, ?_⟩
  rw [Zout, Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) hd).symm) (by have := hs.1.k1024; omega)]
  exact h.zero

theorem budget_vp : VP (RJ2 P) (.block budget) (RJ5 P) :=
  VP.taint [.esp] budget_taint (sp_agree fun _ _ h => h.hs) fun σ s h => by
    have hs := h.hs
    have hml := hs.1.mlK
    have hK := hs.1.k1024
    have hl := hs.1.len1149
    have hpl := hs.1.pl1021
    simp only [budget]
    refine hs.2.wp_arg (j := 10) (r := .eax) (by simp) (by decide) fun t1 s1 u1 => ?_
    refine s1.wp_arg (j := 4) (r := .ebx) (by simp) (by decide) fun t2 s2 u2 => ?_
    refine s2.wp_arg (j := 8) (r := .ecx) (by simp) (by decide) fun t3 s3 u3 => ?_
    refine wp_sub fun t4 u4 _ => wp_addi fun t5 u5 => ?_
    have s5 := (s3.upd u4 (by decide)).upd u5 (by decide)
    refine s5.wp_arg (j := 2) (r := .esi) (by simp) (by decide) fun t6 s6 u6 => ?_
    refine wp_cmp fun t7 u7 c7 _ => WP.block_nil ?_
    have mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    have ax6 : t6.gpr .eax = BitVec.ofNat 32 P.len := by
      rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.other _ (by decide), u1.gpr]; rfl
    have bx6 : t6.gpr .ebx = BitVec.ofNat 32 (P.pl + 128) := by
      rw [u6.other _ (by decide), u5.gpr, u4.gpr, u3.gpr, u3.other .ebx (by decide), u2.gpr]
      show BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ml + BitVec.ofNat 32 125 = _
      rw [sub_ofNat (by omega), BitVec.ofNat_add_ofNat]; congr 1; simp only [RP.pl]; omega
    refine ⟨⟨hs.1, s6.fupd u7⟩, ?_, h.short, by rw [Zout, mm]; exact h.zero, by rw [u7.gpr]; exact ax6,
      by rw [u7.gpr]; exact bx6, by rw [u7.gpr, u6.gpr]; rfl, ?_⟩
    · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.other _ (by decide), u1.other _ (by decide), h.dx]
    · rw [c7, ax6, bx6, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]

/-! ## The outcomes -/

theorem In.nzShort {σ : State} (h : In P σ) (hc : cnt P.mask P.mask.length < P.pl) :
    (nz (rB P σ)).length < P.pl ∧ P.mask.length = P.len := by
  have e := h.cntE (Nat.le_refl _)
  have hn : (nz ((rB P σ).take (scanLen P.pl (rB P σ)))).length < P.pl := by rw [h.scanN, e]; exact hc
  refine ⟨nz_short hn, ?_⟩
  rcases scanLen_end P.pl (rB P σ) with e' | e'
  · omega
  · rw [← h.scanN, e', Proof.RsaPkcs1Sig.bytesAt_len]

theorem exhausted_vp : VP (fun σ s => RJ5 P σ s ∧ isa.eval .ae s = some true) (.block exhausted) (Fin P) :=
  VP.taint [.esi] exhausted_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.si, h₂.1.si]) fun σ s ⟨h, he⟩ => by
    have hs := h.hs
    have hl := hs.1.len1149
    have hge : P.pl + 128 ≤ P.len := by
      change Option.map (!·) s.cf = _ at he; rw [h.cf] at he; simpa using he
    obtain ⟨hnz, hN⟩ := hs.1.nzShort h.short
    have hR : (rB P σ).length = P.len := Proof.RsaPkcs1Sig.bytesAt_len _ _ _
    obtain ⟨ho, hu⟩ := padSearch_exhausted hnz (by rw [hR]; exact hge)
    simp only [exhausted]
    refine wp_stTape hs (o := 0) (by decide) h.si fun t1 s1 g1 m1 f1 => ?_
    refine wp_movi fun t2 u2 => ?_
    have s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    have si2 : t2.gpr .esi = P.tape := by rw [u2.other _ (by decide), g1, h.si]
    refine wp_stTape s2 (o := 4) (by decide) si2 fun t3 s3 g3 m3 f3 => ?_
    refine wp_stTape s3 (o := 8) (by decide) (by rw [g3, si2]) fun t4 s4 g4 m4 f4 => ?_
    refine wp_stTape s4 (o := 12) (by decide) (by rw [g4, g3, si2]) fun t5 s5 g5 m5 f5 => ?_
    refine wp_movi fun t6 u6 => WP.block_nil ⟨⟨hs.1, s5.2.upd u6 (by decide)⟩, ?_⟩
    have f2 : Frame [P.TAPE] t1.mem t2.mem := by rw [u2.mem]; exact Frame.refl _ _
    have fr : Frame [P.TAPE] s.mem t6.mem := by
      rw [u6.mem]; exact f1.trans (f2.trans (f3.trans (f4.trans f5)))
    have mm : t6.mem = (((s.mem.writeW (P.tape.setWidth 64) (BitVec.ofNat 32 P.len)).writeW
        (P.tape.setWidth 64 + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW (P.tape.setWidth 64 + BitVec.ofNat 64 8)
        (0 : BitVec 32)).writeW (P.tape.setWidth 64 + BitVec.ofNat 64 12) (0 : BitVec 32) := by
      rw [u6.mem, m5, m4, m3, u2.mem, m1, BitVec.add_zero, g4, g3, u2.gpr, h.ax]
    unfold Res
    rw [ho, hu, hR, u6.gpr]
    refine ⟨⟨0, ?_, by simp only [Spec.Entropy.Result.Requests, ho]⟩, rfl, ?_⟩
    · rw [mm, words4, zero_append_ofNat (by omega),
        show (0 : BitVec 32) ++ (0 : BitVec 32) = BitVec.ofNat 64 0 by decide]
    · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have ww := hs.1.ok.wrw
        simp only [RP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at ww
        exact ww.1.1) (by have := hs.1.k1024; omega)]
      exact h.zero

theorem reqArgs_vp : VP (fun σ s => RJ5 P σ s ∧ isa.eval .ae s = some false) (.block reqArgs) (RJ6 P) :=
  VP.taint [] reqArgs_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil) fun σ s ⟨h, he⟩ => by
    have hs := h.hs
    have hl := hs.1.len1149
    have hpl := hs.1.pl1021
    have hlt : P.len < P.pl + 128 := by
      change Option.map (!·) s.cf = _ at he; rw [h.cf] at he; simpa using he
    simp only [reqArgs]
    refine wp_add fun t1 u1 _ => wp_cmp fun t2 u2 c2 _ => WP.block_nil ?_
    have ax1 : t1.gpr .eax = BitVec.ofNat 32 (P.len + (P.pl - cnt P.mask P.mask.length)) := by
      rw [u1.gpr, h.ax, h.dx, BitVec.ofNat_add_ofNat]
    have bx1 : t1.gpr .ebx = BitVec.ofNat 32 (P.pl + 128) := by rw [u1.other _ (by decide), h.bx]
    refine ⟨⟨hs.1, (hs.2.upd u1 (by decide)).fupd u2⟩, h.short, by rw [Zout, u2.mem, u1.mem]; exact h.zero,
      by rw [u2.gpr]; exact ax1, by rw [u2.gpr]; exact bx1, by rw [u2.gpr, u1.other _ (by decide)]; exact h.si,
      hlt, ?_⟩
    rw [c2, ax1, bx1, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]

theorem cap_vp : VP (RJ6 P) (.ite .b (.block [.mov .eax (.reg .ebx)]) (.block [])) (RJ7 P) :=
  VP.ite (fun _ _ h => ⟨_, h.cf⟩) (fun _ _ _ _ h₁ h₂ => by
      show eval .b _ = eval .b _; simp only [eval]; rw [h₁.cf, h₂.cf])
    (VP.taint [] movEb_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil) fun σ s ⟨h, he⟩ => by
      have hc : P.pl + 128 < P.len + (P.pl - cnt P.mask P.mask.length) := by
        change s.cf = _ at he; rw [h.cf] at he; simpa using he
      refine wp_mov fun t u => WP.block_nil ⟨⟨h.hs.1, h.hs.2.upd u (by decide)⟩, h.short,
        by rw [Zout, u.mem]; exact h.zero, ?_, by rw [u.other _ (by decide)]; exact h.si, h.lt⟩
      rw [u.gpr, h.bx, Nat.min_eq_left (by omega)])
    (VP.block_nil fun σ s ⟨h, he⟩ => by
      have hc : ¬ P.pl + 128 < P.len + (P.pl - cnt P.mask P.mask.length) := by
        change s.cf = _ at he; rw [h.cf] at he; simpa using he
      exact ⟨h.hs, h.short, h.zero, by rw [h.ax, Nat.min_eq_right (by omega)], h.si, h.lt⟩)

theorem request_vp : VP (RJ7 P) (.block request) (Fin P) :=
  VP.taint [.esi] request_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.si, h₂.si]) fun σ s h => by
    have hs := h.hs
    have hl := hs.1.len1149
    have hpl := hs.1.pl1021
    obtain ⟨hnz, hN⟩ := hs.1.nzShort h.short
    have hR : (rB P σ).length = P.len := Proof.RsaPkcs1Sig.bytesAt_len _ _ _
    obtain ⟨ho, hu⟩ := padSearch_entropy hnz (by rw [hR]; exact h.lt)
    simp only [request]
    refine wp_movi fun t1 u1 => ?_
    have s1 : S P σ t1 := ⟨hs.1, hs.2.upd u1 (by decide)⟩
    have si1 : t1.gpr .esi = P.tape := by rw [u1.other _ (by decide), h.si]
    refine wp_stTape s1 (o := 0) (by decide) si1 fun t2 s2 g2 m2 f2 => ?_
    refine wp_stTape s2 (o := 4) (by decide) (by rw [g2, si1]) fun t3 s3 g3 m3 f3 => ?_
    refine wp_stTape s3 (o := 8) (by decide) (by rw [g3, g2, si1]) fun t4 s4 g4 m4 f4 => ?_
    refine wp_stTape s4 (o := 12) (by decide) (by rw [g4, g3, g2, si1]) fun t5 s5 g5 m5 f5 => ?_
    refine wp_movi fun t6 u6 => WP.block_nil ⟨⟨hs.1, s5.2.upd u6 (by decide)⟩, ?_⟩
    have f1 : Frame [P.TAPE] s.mem t1.mem := by rw [u1.mem]; exact Frame.refl _ _
    have fr : Frame [P.TAPE] s.mem t6.mem := by
      rw [u6.mem]; exact f1.trans (f2.trans (f3.trans (f4.trans f5)))
    have ax1 : t1.gpr .eax = BitVec.ofNat 32 (min (P.pl + 128) (P.len + (P.pl - cnt P.mask P.mask.length))) := by
      rw [u1.other _ (by decide), h.ax]
    have mm : t6.mem = (((t1.mem.writeW (P.tape.setWidth 64) (0 : BitVec 32)).writeW
        (P.tape.setWidth 64 + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW (P.tape.setWidth 64 + BitVec.ofNat 64 8)
        (BitVec.ofNat 32 (min (P.pl + 128) (P.len + (P.pl - cnt P.mask P.mask.length))))).writeW
        (P.tape.setWidth 64 + BitVec.ofNat 64 12) (0 : BitVec 32) := by
      rw [u6.mem, m5, m4, m3, m2, BitVec.add_zero, g4, g3, g2, u1.gpr, ax1]
    unfold Res
    rw [ho, hu, u6.gpr]
    refine ⟨⟨min (P.pl + 128) (P.len + (P.pl - cnt P.mask P.mask.length)), ?_, ?_⟩, rfl, ?_⟩
    · rw [mm, words4, zero_append_ofNat (by omega),
        show (0 : BitVec 32) ++ (0 : BitVec 32) = BitVec.ofNat 64 0 by decide]
    · simp only [Spec.Entropy.Result.Requests, ho, Spec.Entropy.RequestValid, Spec.RsaPkcs1Enc.padEntropy]
      have := h.short
      rw [hR]
      exact ⟨Nat.lt_min.mpr ⟨h.lt, by omega⟩, Nat.min_le_left _ _⟩
    · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have ww := hs.1.ok.wrw
        simp only [RP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at ww
        exact ww.1.1) (by have := hs.1.k1024; omega)]
      exact h.zero

theorem reject_vp : VP (fun σ s => Dz P σ s ∧ isa.eval .e s = some false) reject (Fin P) :=
  (zeroOut_vp (P := P)).1.seq (zeroOut_vp.2.seq (drawnArgs_vp.seq (drawn_vp.seq ((budget_vp (P := P)).seq (VP.ite (fun _ _ h => ⟨_, by
      show Option.map (!·) _ = _; rw [h.cf]; rfl⟩)
    (fun _ _ _ _ h₁ h₂ => by show eval .ae _ = eval .ae _; simp only [eval]; rw [h₁.cf, h₂.cf])
    exhausted_vp (reqArgs_vp.seq (cap_vp.seq request_vp)))))))

end VG.Proof.RsaPkcs1Enc.X86.Rnd
