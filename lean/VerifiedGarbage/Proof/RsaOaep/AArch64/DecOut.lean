import VerifiedGarbage.Proof.RsaOaep.AArch64.DecLoops

/-!
# RSAES-OAEP decryption on AArch64: the outputs

As on x86-64 (`Proof/RsaOaep/X86_64/DecOut.lean`): the mask `ok`
(`okMask_ok`), the buffer ANDed with it to `out` (`outLoop_ok`), the length
and the result (`decRet_ok`), and zeros to `out` (`zeroOut_ok`, which
encryption's failure uses too).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- A region apart from the frame, our working space and the stack below
the frame. -/
structure Apart (F S : Addr) (r : Region) : Prop where
  dF : Region.Disjoint r ⟨F, frameBytes⟩
  dS : Region.Disjoint r ⟨S, oRsa⟩
  dK : Region.Disjoint r (retR F)

/-- What a step in `r`, apart from the frame and our working space, leaves of `Rep`. -/
theorem Rep.apart {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (_ : Geo F S)
    (R : Rep m F S V W) {r : Region} (ha : Apart F S r) (hf : Frame [r] m m') : Rep m' F S V W where
  scr o ho := by
    rw [hf _ fun r' hr' hc => ?_]
    · exact R.scr o ho
    rw [List.mem_singleton.mp hr'] at hc
    exact ha.dS _ hc ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide))
  fr k hk := by
    rw [word, hf.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)]
    · exact R.fr k hk
    rw [List.mem_singleton.mp hr']
    exact (ha.dF.sub_right (Offset.sub_base F (by unfold nW frameBytes at *; omega))).symm

/-! ## `ok` -/

/-- `ok`: all ones iff the private-key operation's result `r` (word 28) is 1
and the accumulator (word 29) is zero. -/
def okW (W : Nat → BitVec 64) : BitVec 64 := zM (W 29) &&& zM (W 28 ^^^ 1)

theorem okMask_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block okMask) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S V (upd W 31 (okW W)) := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 248) 8 (okW W)) F S V (upd W 31 (okW W)) := R.wq G' (k := 31) (by decide) _
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  have h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have w248 : InRegions u.wr (F + BitVec.ofNat 64 248) 8 := L.st (d := 248) (by decide)
  have rr := R.rd8 (d := 224) (k := 28) rfl (by decide) rfl
  have ra := R.rd8 (d := 232) (k := 29) rfl (by decide) rfl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 248) 8 (okW W) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [okMask, isZero, sR, sAcc, sOk, h224, h232, w248, L.sp, rr, ra, BitVec.add_zero, sbc_one, okW,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide]
    oaep_fin
  have R' : Rep u'.mem F S V (upd W 31 (okW W)) := by rw [hm]; exact R1
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))

end VG.Proof.RsaOaep.AArch64
