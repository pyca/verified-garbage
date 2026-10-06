import VerifiedGarbage.Proof.RsaPss.AArch64.CtPadEq

/-!
# RSASSA-PSS on AArch64: hashing a message of secret length

`ctHashWith padding` leaves the digest of the first `ℓ` bytes of `Y` at
`scratch + oDig` (`ctHashWith_ok`), from a state where those bytes are
followed by zeros up to `nbm` blocks, for a padding step that ORs `0x80`
into byte `ℓ` (`pad80` or `fixedPad80`). It keeps everything but our part
of the working space before `oEm` and from `oY` on.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPss (padded lastBlk pad_getD pad_length)

theorem bytesAt_writeBytes_take (m : Mem) (q : Addr) (xs : List Byte) {d : Nat} (hd : d ≤ xs.length)
    (hl : xs.length < 2 ^ 64) : Spec.Rsa.bytesAt (writeBytes m q xs) q d = xs.take d := by
  conv_rhs => rw [← VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes m q xs hl]
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hd]

/-- What `ctHash` keeps of the state `t`. -/
structure CtOut (t : State) (F S : Addr) (V : Nat → Byte) (t' : State) : Prop where
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28], t'.gpr r = t.gpr r
  vec : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame [⟨S, oRsa⟩, below F 16] t.mem t'.mem
  em : ∀ o, oEm ≤ o → o < oY → t'.mem (off S o) = V o

section
variable {H : Hash} (hH : HashOK H)

/-- The streaming `init` on `scratch + oSt`. -/
theorem ctInit_ok {t : State} {F S : Addr} (L : Lay t F S) (h19 : t.gpr .x19 = off S oSt) :
    WP isa (ctInit H) t fun u => u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame [⟨off S oSt, H.P.N + H.P.B⟩, below F 16] t.mem u.mem ∧
      hH.md.stateAt u.mem (off S oSt) = hH.iv := by
  have hN := hH.N_le; have hBl := hH.B_le
  unfold ctInit
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_nil ?_)
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.init_call hH.stream (st := off S oSt) (by rw [e₁, h19])
    (by rw [o₁.wr]; exact Covers.one (L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega))) fun u hA hr => ?_
  refine ⟨by rw [hA.sp, o₁.sp], by rw [hA.rd, o₁.rd], by rw [hA.wr, o₁.wr], fun r hr h30 => ?_,
    fun r hr => by rw [hA.vec r hr, o₁.vcs r hr], ?_, ?_⟩
  · rw [hA.cs r hr h30, o₁.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)]
  · have := hA.frame
    rw [o₁.mem, o₁.sp, L.sp] at this
    exact this
  · obtain ⟨h1, -⟩ := (hH.repr _ _ _).1 hr
    rw [h1, List.length_nil, Nat.zero_div, Md.compressList_zero]

/-- The digest of the hash value at `scratch + oSel` to `scratch + oDig`. -/
theorem digestOut_ok {t : State} {F S : Addr} (L : Lay t F S) (h21 : t.gpr .x21 = off S oDig) :
    WP isa (.block (digestOut H)) t fun t' => Keep [.x19, .x9] t t' ∧ t'.gpr .x19 = off S oSt ∧
      t'.mem = writeBytes t.mem (off S oDig) (hH.md.digest (hH.md.stateAt t.mem (off S oSel))) := by
  have hN := hH.N_le
  unfold digestOut
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => ?_
  show WP isa (.block (H.P.out ++ [.addImm .x .x19 .x20 oSt])) u₁ _
  rw [WP.block_append_iff]
  have h19 : u₁.gpr .x19 = off S oSel := by rw [e₁, L.x20]
  have r19 : InRegions (u₁.rd ++ u₁.wr) (u₁.gpr .x19) H.P.N := by
    rw [h19, o₁.rd, o₁.wr]; exact L.ld (by unfold oSel oRsa; omega)
  have w21 : InRegions u₁.wr (u₁.gpr .x21) H.P.N := by
    rw [o₁.get .x21, h21, o₁.wr]; exact L.st (by unfold oDig oRsa; omega)
  have d : Region.Disjoint ⟨u₁.gpr .x19, H.P.N⟩ ⟨u₁.gpr .x21, H.P.N⟩ := by
    rw [h19, o₁.get .x21, h21]
    exact Offset.disjoint _ (by unfold oSel oDig; omega) (by unfold oSel; omega) (by unfold oDig; omega)
  refine WP.mono (WP.preservedV (hH.shape.out u₁ r19 w21 d)
      (by rw [Code.allInstrs_eq]; exact hH.shape.outKeepsV))
    fun u₂ ⟨⟨hg, hrd, hwr, hsp, hm⟩, hv⟩ => ?_
  refine wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simpa using hr.1), hg r hr.2, o₁.gpr r (by simpa using hr.1)]
  · rw [o₃.rd, hrd, o₁.rd]
  · rw [o₃.wr, hwr, o₁.wr]
  · rw [o₃.sp, hsp, o₁.sp]
  · rw [o₃.vcs r hr, hv r hr, o₁.vcs r hr]
  · rw [e₃, hg .x20 (by decide), o₁.get .x20, L.x20]
  · rw [o₃.mem, hm, h19, o₁.get .x21, h21, o₁.mem]

end

end VG.Proof.RsaPss.AArch64
