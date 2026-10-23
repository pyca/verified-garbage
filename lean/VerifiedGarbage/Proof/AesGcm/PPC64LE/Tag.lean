module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on PPC64LE: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag d o` absorbs the lengths
block of `r21` bytes of additional data and `r22` bytes of text into the
accumulator at `St + 16` (`lens 16`), copies the accumulator to
`Dt = d + o`, and XORs `CIPH_K(J₀)` into it with `vg_aes_ctr32` on the
counter block `J₀` at `St` (`tag_wp`), which it leaves incremented.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gcm
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_ld wp_std)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith toBytes ofBytes)
open VG.Spec.Aes (bytesAt)

/-- The regions `tag` writes: `J₀` and the accumulator, `W` and the tag. -/
abbrev tagRs (W St Dt : Addr) : List Region := [⟨St, 32⟩, wR W, ⟨Dt, 16⟩]

/-- What `tag d o` needs: `lens 16`'s, the rounds, and the 16 bytes at
`Dt = d + o` writable and apart from `St`, the key context and the first
2048 bytes of `W`. -/
structure TagPre (s : State) (W St C : Addr) (R a c : Nat) (d : Reg) (o : Nat) (Dt : Addr) : Prop where
  lens : LensPre s W St C 16 a c
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  r17 : s.gpr .r17 = BitVec.ofNat 64 R
  hd : s.gpr d + BitVec.ofNat 64 o = Dt
  hdk : d ∈ keepRegs
  hdr : d ≠ .r0 ∧ d ≠ .r5 ∧ d ≠ .r6
  ho : o + 8 < 2 ^ 15 ∧ o % 4 = 0
  dw : Covers [⟨Dt, 16⟩] s.wr
  dst : (⟨Dt, 16⟩ : Region).Disjoint (stR St)
  dc : (⟨Dt, 16⟩ : Region).Disjoint (cR C)
  dsc : (⟨Dt, 16⟩ : Region).Disjoint ⟨W, 2048⟩
  fit : Dt.toNat + 16 ≤ 2 ^ 64

/-- What `tag` does: `GHASH ⊕ CIPH_K(J₀)` at `Dt`. -/
structure TagPost (s₀ : State) (W St C : Addr) (R a c : Nat) (Dt : Addr) (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame (tagRs W St Dt) s₀.mem s.mem
  out : bytesAt s.mem Dt 16 =
    toBytes (ghashFrom (hk s₀.mem C) (blockAt s₀.mem (St + BitVec.ofNat 64 16)) [ofBytes (lensBlock a c)] ^^^
      cph s₀.mem C R (blockAt s₀.mem St))

theorem keep_args : ∀ r ∈ keepRegs, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 := by
  decide

theorem bytesAt_toBytes (m : Mem) (p : Addr) : bytesAt m p 16 = toBytes (blockAt m p) :=
  (Proof.Cmac.toBytes_ofBytes (length_bytesAt' _ _ _)).symm

/-- Two doublewords copied are 16 bytes copied. -/
theorem copy16 (m m' : Mem) (Dt S : Addr) :
    (m'.writeW Dt (m.readW S 64)).writeW (Dt + BitVec.ofNat 64 8) (m.readW (S + BitVec.ofNat 64 8) 64) =
      writeBytes m' Dt (bytesAt m S 16) := by
  rw [VG.Proof.Gather.PPC64LE.writeW_readW, VG.Proof.Gather.PPC64LE.writeW_readW,
    show Dt + BitVec.ofNat 64 8 = Dt + BitVec.ofNat 64 (bytesAt m S 8).length by rw [length_bytesAt'],
    writeBytes_append _ _ _ _ (by simp [length_bytesAt']), bytesAt_split]

theorem tag_wp {s : State} {W St C : Addr} {R a c : Nat} {d : Reg} {o : Nat} {Dt : Addr}
    (hp : TagPre s W St C R a c d o Dt) : WP isa (tag d o) s (TagPost s W St C R a c Dt) := by
  have he := hp.lens.env
  have ho := hp.ho
  unfold tag
  refine WP.seq (WP.mono (lens_wp hp.lens) fun s₁ L => ?_)
  have he₁ := he.of_pk L.pk
  have hd₁ : s₁.gpr d = s.gpr d := L.pk.gpr d hp.hdk
  unfold tagArgs
  refine WP.seq (wp_ld (a := St + BitVec.ofNat 64 16) (by decide) (by decide) (by rw [he₁.r15])
    (he₁.stRdR (d := 16) (n := 8) (by decide)) fun s₂ u₂ => ?_)
  have rd₂ : InRegions (s₂.rd ++ s₂.wr) (St + BitVec.ofNat 64 24) 8 := by
    rw [u₂.rd, u₂.wr]; exact he₁.stRdR (d := 24) (n := 8) (by decide)
  refine wp_ld (a := St + BitVec.ofNat 64 24) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), he₁.r15]) rd₂ fun s₃ u₃ => ?_
  have hd₃ : s₃.gpr d = s.gpr d := by
    rw [u₃.other _ hp.hdr.2.2, u₂.other _ hp.hdr.2.1, hd₁]
  have dw₁ : Covers [⟨Dt, 16⟩] s₃.wr := by rw [u₃.wr, u₂.wr, L.pk.wr]; exact hp.dw
  have w₀ : InRegions s₃.wr Dt 8 := by
    have := VG.Proof.Gather.PPC64LE.in_off (d := 0) (n := 8) dw₁ (by decide) (by decide)
    simpa only [BitVec.add_zero] using this
  refine wp_std (a := Dt) hp.hdr.1 ⟨by omega, hp.ho.2⟩ (by rw [hd₃, hp.hd]) w₀ fun s₄ u₄ => ?_
  refine wp_std (a := Dt + BitVec.ofNat 64 8) hp.hdr.1 ⟨hp.ho.1, by omega⟩
    (by rw [u₄.gpr, hd₃, ← hp.hd, add_ofNat_add])
    (by rw [u₄.wr]; exact VG.Proof.Gather.PPC64LE.in_off (d := 8) dw₁ (by decide) (by decide))
    fun s₅ u₅ => ?_
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_addi hp.hdr.1 (by omega)
    fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_
  have pk₁₁ : PK s₁ s₁₁ := (PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁)))))))))
  have m₁₁ : s₁₁.mem = writeBytes s₁.mem Dt (bytesAt s₁.mem (St + BitVec.ofNat 64 16) 16) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem,
      u₃.other .r5 (by decide), u₂.gpr, u₂.mem, show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 +
        BitVec.ofNat 64 8 by rw [add_ofNat_add]]
    exact copy16 _ _ _ _
  have frD : Frame [⟨Dt, 16⟩] s₁.mem s₁₁.mem := by
    rw [m₁₁]; exact Proof.AesGcm.writeBytes_frame' _ (length_bytesAt' _ _ _)
  have hDt : blockAt s₁₁.mem Dt = blockAt s₁.mem (St + BitVec.ofNat 64 16) := by
    simp only [blockAt]
    have hw := Proof.AesGcm.bytesAt_writeBytes_self s₁.mem Dt
      (bytesAt s₁.mem (St + BitVec.ofNat 64 16) 16) (by rw [length_bytesAt']; decide)
    rw [length_bytesAt'] at hw
    rw [m₁₁, hw]
  -- `J₀` and the key schedule are what they were.
  have frS : Frame (ghRs W St 16 ++ [⟨Dt, 16⟩]) s.mem s₁₁.mem :=
    (L.frame.mono fun r hr => List.mem_append_left _ hr).trans
      (frD.mono fun r hr => List.mem_append_right _ hr)
  have hJ : blockAt s₁₁.mem St = blockAt s.mem St := by
    simp only [blockAt]
    refine congrArg ofBytes (Proof.Cmac.bytesAt_frame (n := 16) frS (fun r hr => ?_) (by decide))
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · simpa only [BitVec.add_zero] using he.st_st (d := 0) (n := 16) (e := 16) (k := 16) (by omega)
        (by decide) (by decide)
    · exact (he.sw.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.dst.sub_right (Region.sub_prefix (by decide))).symm
  have hR : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have hkey : bytesAt s₁₁.mem C (16 * (R + 1)) = bytesAt s.mem C (16 * (R + 1)) := by
    have hs : Region.Sub ⟨C, 16 * (R + 1)⟩ (cR C) := Region.sub_prefix (by omega)
    refine Proof.Cmac.bytesAt_frame (n := 16 * (R + 1)) frS (fun r hr => ?_) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact (he.cs.sub_left hs).sub_right (Offset.sub_base _ (by decide))
    · exact (he.cw.sub_left hs).sub_right (Region.sub_prefix (by decide))
    · exact (hp.dc.sub_right hs).symm
  have he₁₁ := he₁.of_pk pk₁₁
  have hcp : CtrPre s₁₁ C R St Dt W 1 := by
    have c0 : Region.Disjoint ⟨C, 240⟩ ⟨St, 16⟩ := by
      have := he.c_st (d := 0) (n := 240) (e := 0) (k := 16) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hp.rounds, by omega, c0,
      ((hp.dc.sub_right (Region.sub_prefix (by decide))).symm.sub_right (Region.sub_prefix (by decide))),
      ?_, ((hp.dst.sub_right (Region.sub_prefix (by decide))).symm.sub_right (Region.sub_prefix (by decide))),
      ?_, by simpa using hp.dsc, by have := hp.fit; omega, ?_, ?_⟩
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        he₁.r16]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        L.pk.gpr .r17 (by decide), hp.r17]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), he₁.r15]
    · have hdn := keep_args d hp.hdk
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ hdn.2.2.1,
        u₇.other _ hdn.2.1, u₆.other _ hdn.1, u₅.gpr, u₄.gpr, hd₃, hp.hd]
    · rw [u₁₁.other _ (by decide), u₁₀.gpr]
    · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), he₁.r14]
    · have := he.c_w (d := 0) (n := 240) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · have := he.st_w (d := 0) (n := 16) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · rw [pk₁₁.rd, pk₁₁.wr, L.pk.rd, L.pk.wr]
      refine Covers.append_left ?_ (Covers.cons ?_ (Covers.pair (VG.Covers.right
        (by simpa using hp.dw)) ?_))
      · have := he.cIn (d := 0) (n := 240) (by decide); simpa only [BitVec.add_zero] using this
      · have := he.stRd (d := 0) (n := 16) (by decide); simpa only [BitVec.add_zero] using this
      · have := he.wRd (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
    · rw [pk₁₁.wr, L.pk.wr]
      refine Covers.cons ?_ (Covers.pair (by simpa using hp.dw) ?_)
      · have := he.stIn (d := 0) (n := 16) (by decide); simpa only [BitVec.add_zero] using this
      · have := he.wIn (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
  refine WP.mono (ctr_call hcp) fun s' ⟨ck, hd', _⟩ => ⟨L.pk.trans (pk₁₁.trans (PK.ofCall ck)), ?_, ?_⟩
  · refine Frame.trans (L.frame.sub fun r hr => ?_) ((frD.sub fun r hr => ?_).trans (ck.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 32⟩, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
      · exact ⟨wR W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨Dt, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 32⟩, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨⟨Dt, 16⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨wR W, by simp, sub_wR0 (by decide)⟩
  · rw [blocksAt_one, blocksAt_one, hkey, hJ, hDt, L.y] at hd'
    simp only [ctr32, Spec.Gcm.keystream, List.range_one, List.map_cons, List.map_nil,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.length_singleton, List.cons.injEq,
      and_true] at hd'
    rw [bytesAt_toBytes, hd']
    rfl

end VG.Proof.AesGcm.PPC64LE
