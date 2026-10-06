import VerifiedGarbage.Proof.RsaOaep.AArch64.Args

/-!
# RSAES-OAEP encryption on AArch64: `EM` before masking

The pieces that write `EM` to our working space (as on x86-64,
`Proof/RsaOaep/X86_64/EncEm.lean`): its place cleared (`clearEm_ok`), the
seed (`copySeed_ok`) and `lHash` (`copyLh_ok`) copied to it, and `0x01` and
the message (`putMsg_ok`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

section
variable {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
  (R : Rep u.mem F S V W)
include L R

theorem clearEm_ok : WP isa clearEm u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S (zV V oEm 1024) W := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oEm ∧
      u'.gpr .x12 = BitVec.ofNat 64 128 ∧ u'.gpr .x13 = 0) ?_ fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [clearEm, scr, Mgf1.scr, lay, sScr, oEm, h96, L.sp, hs]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (clearLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) (o := oEm) (n := 128) (by decide)
    (by decide) x11 x12 x13 []) fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, R2⟩

/-- The seed (`D` bytes at `sd`, in the slot of `seed`) to `EM + 1`. -/
theorem copySeed_ok {H : Hash} {sd : Addr} (hsd : W 29 = sd) (hD : 0 < H.D) (hD' : H.D ≤ 64)
    (hA : ∀ i < H.D, InRegions (u.rd ++ u.wr) (off sd i) 1)
    (hne : ∀ i < H.D, ∀ j < H.D, off sd i ≠ off S (oEm + 1 + j)) :
    WP isa (copySeed H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (cpV V (oEm + 1) H.D fun i => u.mem (off sd i)) W := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rsd := R.rd8 (d := 232) (k := 29) rfl (by decide) hsd
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = sd ∧
      u'.gpr .x12 = off S (oEm + 1) ∧ u'.gpr .x13 = BitVec.ofNat 64 H.D) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [copySeed, scr, Mgf1.scr, lay, sScr, sSeed, h96, h232, L.sp, hs, rsd,
      show oEm + 1 < 4096 by decide, imm16 (show H.D < 65536 by omega)]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (copyLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) (A := sd) (b := oEm + 1) (n := H.D) hD
    (by unfold oEm oRsa; omega) (fun i hi => by rw [hrd, hwr]; exact hA i hi) hne x11 x12 x13 [])
    fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, by rw [hm] at R2; exact R2⟩

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + D`. -/
theorem copyLh_ok {H : Hash} (hD : 0 < H.D) (hD' : H.D ≤ 64) :
    WP isa (copyLh H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (cpV V (oEm + 1 + H.D) H.D fun i => V (oDig + i)) W := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S (oEm + 1 + H.D) ∧ u'.gpr .x13 = BitVec.ofNat 64 H.D) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [copyLh, scr, Mgf1.scr, lay, sScr, h96, L.sp, hs, show oDig < 4096 by decide,
      show oEm + 1 + H.D < 4096 by unfold oEm; omega, imm16 (show H.D < 65536 by omega)]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  have L1 : Lay u1 F S := L.congr hsp hwr (by rw [hm])
  have c : oRsa = 8192 := rfl
  have hA : ∀ i < H.D, InRegions (u1.rd ++ u1.wr) (off (off S oDig) i) 1 := fun i hi => by
    rw [off_off]; exact L1.sld (by unfold oDig; omega)
  have hne : ∀ i < H.D, ∀ j < H.D, off (off S oDig) i ≠ off S (oEm + 1 + H.D + j) := fun i hi j hj => by
    rw [off_off]; exact Offset.add_ofNat_ne S (by unfold oDig; omega) (by unfold oEm; omega)
      (by unfold oDig oEm; omega)
  refine WP.mono (copyLoop_ok L1 (hm ▸ R) (A := off S oDig) (b := oEm + 1 + H.D) (n := H.D) hD
    (by unfold oEm; omega) hA hne x11 x12 x13 [])
    fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, ?_⟩
  refine (congrArg (fun V' => Rep u2.mem F S V' W) (funext fun x => ?_)).mp R2
  simp only [cpV]
  split
  · rw [off_off, hm, R.scr _ (by unfold oDig; omega)]
  · rfl

/-- `0x01` at `EM + k - mLen - 1`, and the message (`mLen` bytes at `msg`)
after it. -/
theorem putMsg_ok {k mLen : Nat} {msg : Addr} (hk : W 21 = BitVec.ofNat 64 k) (hml : W 28 = BitVec.ofNat 64 mLen)
    (hmsg : W 27 = msg) (hkm : mLen + 1 ≤ k) (hk' : k ≤ 1024)
    (hA : ∀ i < mLen, InRegions (u.rd ++ u.wr) (off msg i) 1)
    (hne : ∀ i < mLen, ∀ j < oRsa, off msg i ≠ off S j) :
    WP isa putMsg u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (cpV (upd V (k - mLen - 1) 1) (k - mLen) mLen fun i => u.mem (off msg i)) W := by
  have G' := L.geo
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h216 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  have rml := R.rd8 (d := 224) (k := 28) rfl (by decide) hml
  have rmsg := R.rd8 (d := 216) (k := 27) rfl (by decide) hmsg
  have c : oRsa = 8192 := rfl
  have hsub : ∀ x y : BitVec 64, S + x - y = S + (x - y) := fun x y => by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have e1 : S + BitVec.ofNat 64 oEm + BitVec.ofNat 64 k - BitVec.ofNat 64 mLen - BitVec.ofNat 64 1 =
      off S (k - mLen - 1) := by
    rw [show oEm = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hsub, hsub,
      Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega)]
  have w1 : InRegions u.wr (off S (k - mLen - 1)) 1 := L.sst (by omega)
  have R1 : Rep (u.mem.write (off S (k - mLen - 1)) 1
      (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 1)))) F S (upd V (k - mLen - 1) 1) W :=
    R.wb G' (by omega) _
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off S (k - mLen - 1)) 1
      (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 1))) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = msg ∧
      u'.gpr .x12 = off (off S (k - mLen - 1)) 1 ∧ u'.gpr .x13 = BitVec.ofNat 64 mLen) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [putMsg, scr, Mgf1.scr, lay, sScr, sK, sMsgLen, sMsg, h96, h168, h216, h224, L.sp, hs, rk, rml,
      rmsg, e1, w1, BitVec.add_zero, show oEm < 4096 by decide,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = BitVec.ofNat 64 1 by decide]
    oaep_fin
  have R1' : Rep u1.mem F S (upd V (k - mLen - 1) 1) W := by rw [hm]; exact R1
  have L1 : Lay u1 F S := L.congr hsp hwr (by rw [show sScr = 8 * 12 from rfl, R1'.fr 12 (by decide),
    R.fr 12 (by decide)])
  have S1 : Step F S [] u u1 := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    rw [hm]; exact frame_wb (Frame.refl _ _) (by omega) _⟩
  have hmA : ∀ i < mLen, u1.mem (off msg i) = u.mem (off msg i) := fun i hi => by
    rw [hm, write1_apply, ifn (hne i hi _ (by omega))]
  have e0 : cpV (upd V (k - mLen - 1) 1) (k - mLen) mLen (fun i => u.mem (off msg i)) =
      cpV (upd V (k - mLen - 1) 1) (k - mLen) mLen (fun i => u1.mem (off msg i)) := by
    funext x; simp only [cpV]; split
    · rw [hmA _ (by omega)]
    · rfl
  rw [e0]
  refine WP.ite _ (eval_nonzero u1 .x13) (fun hb => ?_) (fun hb => ?_)
  · have hm0 : 0 < mLen := by
      rw [x13] at hb
      have h0 : BitVec.ofNat 64 mLen ≠ 0 := by simpa using hb
      by_contra h; exact h0 (by rw [show mLen = 0 by omega]; rfl)
    refine WP.mono (copyLoop_ok L1 R1' (A := msg) (b := k - mLen) (n := mLen) hm0 (by omega)
      (fun i hi => by rw [hrd, hwr]; exact hA i hi) (fun i hi j hj => hne i hi _ (by omega)) x11
      (by rw [x12, off_off, show k - mLen - 1 + 1 = k - mLen by omega]) x13 [])
      fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, R2⟩
  · have hm0 : mLen = 0 := by
      rw [x13] at hb
      by_contra h
      have : BitVec.ofNat 64 mLen ≠ 0 := fun e => h (by
        have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this)
      simp at hb
      exact this hb
    subst hm0
    refine WP.block_nil ⟨L1, S1, ?_⟩
    refine (congrArg (fun V' => Rep u1.mem F S V' W) (funext fun x => ?_)).mp R1'
    simp only [cpV]; rw [ifn (by omega)]

end

end VG.Proof.RsaOaep.AArch64
