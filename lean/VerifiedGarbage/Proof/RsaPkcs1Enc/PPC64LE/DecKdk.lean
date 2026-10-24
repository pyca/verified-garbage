module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecMac
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: `KDK = HMAC(DH, C)`

HMAC-SHA-256 keyed with `DH`, of the ciphertext, to `scratch + sKDK`
(`kdkMac_ok`, from `DHS` to `KD`), and the argument blocks of HMAC's `init`
for any key in `scratch` (`macInitArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

/-- The ciphertext. -/
abbrev cOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .r7).toNat

/-- The private exponent. -/
abbrev dOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat

/-- After `kdkMac`: `KDK` at `scratch + sKDK`. -/
structure KD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  post : Post s R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length := by
  simp [Spec.Hmac.xorPad]

section
variable {s : State} {R : BitVec 64} {EM : List Byte}

theorem macInitArgs_ok {t : State} (hc : Post s R EM t) {key : Nat} (hk : key < 2 ^ 15) :
    WP isa (.block (macInitArgs key)) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = scA s sOuter ∧ u.gpr .r5 = scA s key ∧ u.gpr .r6 = BitVec.ofNat 64 32 ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sSt < 2 ^ 15 := by decide
  have c3 : sOuter < 2 ^ 15 := by decide
  have c4 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold macInitArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, hk, i1, hc.sl.scr, exec_addi (show Reg.r3 ≠ .r0 by decide) c2,
    exec_addi (show Reg.r4 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) hk,
    exec_addi (show Reg.r7 ≠ .r0 by decide) c4]

theorem kdkUpdArgs_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block kdkUpdArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = BitVec.ofNat 64 64 ∧ u.gpr .r5 = stackArg s 1 ∧ u.gpr .r6 = s.gpr .r7 ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oIn < 2 ^ 15 ∧ oIn % 4 = 0 := by decide
  have c3 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c4 : sSt < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oIn) (by decide) (by decide)
  have i3 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold kdkUpdArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, i3, hc.sl.scr, hc.sl.inp, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c4, exec_addi (show Reg.r7 ≠ .r0 by decide) c5]

theorem kdkFinArgs_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block kdkFinArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = scA s sOuter ∧ u.gpr .r5 = s.gpr .r7 + BitVec.ofNat 64 64 ∧ u.gpr .r6 = scA s sKDK ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c3 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c4 : sSt < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have c6 : sOuter < 2 ^ 15 := by decide
  have c7 : sKDK < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i3 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold kdkFinArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c3, c4, c5, c6, c7, i1, i3, hc.sl.scr, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c4, exec_addi (show Reg.r4 ≠ .r0 by decide) c6,
    exec_addi (show Reg.r5 ≠ .r0 by decide) (show 64 < 2 ^ 15 by decide),
    exec_addi (show Reg.r6 ≠ .r0 by decide) c7, exec_addi (show Reg.r7 ≠ .r0 by decide) c5]

end

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- The ciphertext misses `scratch` and the stack. -/
theorem cR_eq : (⟨stackArg s 1, (s.gpr .r7).toNat⟩ : Region) = iR s := by simp only [iR, h.hi]

theorem c_sc {a l : Nat} (ha : a + l ≤ scrBytes) : Region.Disjoint ⟨stackArg s 1, (s.gpr .r7).toNat⟩ ⟨scA s a, l⟩ := by
  rw [cR_eq h]; exact (h.is.sub_right (sc_sub h)).sub_right (scSub ha)

theorem c_low {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) :
    (below (fb s) n).Disjoint ⟨stackArg s 1, (s.gpr .r7).toNat⟩ := by
  rw [cR_eq h]; exact h.ki.sub_left (sub_trans (low_sub s hn) (callee_sub s))

theorem c_cov {t : State} (hc : Post s R EM t) : Covers [⟨stackArg s 1, (s.gpr .r7).toNat⟩] (t.rd ++ t.wr) := by
  rw [cR_eq h]
  exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hc.rd, h.hrd]; simp)

theorem c_bytes {t : State} (hc : Post s R EM t) :
    Spec.Rsa.bytesAt t.mem (stackArg s 1) (s.gpr .r7).toNat = cOf s :=
  bytes_frame hc.mem (fun r hr => by
    rw [cR_eq h]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ki.symm
    · exact h.oi.symm
    · exact h.is) (by have := h.k2; omega)

theorem kdkMac_ok {t : State} (hd : DHS s R EM t) : WP isa kdkMac t (KD s R EM) := by
  have hk := h.k2
  have hK : sDH < 2 ^ 15 := by decide
  refine WP.seq (WP.mono (macInitArgs_ok hd.post hK) fun u ⟨⟨um, u3, u4, u5, u6, u7⟩, ku⟩ => ?_)
  have hu : Post s R EM u := hd.post.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  refine WP.seq (macInit_call h hu (by decide) (by decide) u3 u4 u5 u6 u7 fun v hv hI hO hf => ?_)
  refine WP.seq (WP.mono (kdkUpdArgs_ok hv) fun w ⟨⟨wm, w3, w4, w5, w6, w7⟩, kw⟩ => ?_)
  have hw : Post s R EM w := hv.regs kw.rd kw.wr kw.sp wm fun r hr => kw.gpr r (by revert r; decide)
  -- the key
  have k0l : (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u.mem (scA s sDH) 32)).length = 64 :=
    blockKey_length (by simp [Spec.Sha256.bytesAt])
  refine WP.seq (upd_call h hw w3 w5 (by rw [w6]) w7 (c_sc h (by decide)) (c_sc h (by decide)) (c_low h (by decide))
    (c_cov h hw) fun x hx hI' hf' => ?_)
  refine WP.seq (WP.mono (kdkFinArgs_ok hx) fun y ⟨⟨ym, y3, y4, y5, y6, y7⟩, ky⟩ => ?_)
  have hy : Post s R EM y := hx.regs ky.rd ky.wr ky.sp ym fun r hr => ky.gpr r (by revert r; decide)
  refine macFin_call h hy (by decide) (by decide) y3 y4 y6 y7 fun z hz hmac _ => ⟨hz, ?_⟩
  have hO' : hH.SH.Repr y.mem (scA s sOuter)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u.mem (scA s sDH) 32)) Spec.Hmac.opad) := by
    rw [ym]
    refine hH.repr_keep hf' (by rw [xorPad_length, k0l]; rfl) (fun r hr => ?_) (wm ▸ hO)
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact scD h (by decide) (by decide) (by decide)
    · exact scD h (by decide) (by decide) (by decide)
    · exact (lowD h (by decide) (by decide)).symm
  have e := hmac _ (Spec.Rsa.bytesAt w.mem (stackArg s 1) (s.gpr .r7).toNat) k0l
    (by rw [k0l]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega)
    (by rw [ym]; exact hI' _ (wm ▸ hI) (by rw [w4, xorPad_length, k0l]))
    (by
      rw [y5]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hO'
  rw [c_bytes h hw, um] at e
  show Spec.Sha256.bytesAt z.mem (scA s sKDK) 32 = _
  rw [e]
  show Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt t.mem (scA s sDH) 32))
    (cOf s) = _
  rw [hd.dh]; rfl

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
