module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP on ARMv7: the label's hash

`argG`: an argument of the function, read from the frames. `label_vp`: with
the label in the arguments `j` (its address) and `j + 1` (its length), a
range of bytes the body may read whose bytes do not change, `hashLabel`
writes `H(label)` to `scratch + o`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32}

/-- An argument: its place, readable, and its value. -/
theorem argG (hg : Geo L scr) {σ s : State} (hs : L.St σ s) {j : Nat} (hj : j < L.argv.length) :
    State.addr (L.B + BitVec.ofNat 32 (arg j)) = L.fr (arg j) ∧ InRegions (s.rd ++ s.wr) (L.fr (arg j)) 4 ∧
    s.mem.readW (L.fr (arg j)) 32 = L.argv.getD j 0 := by
  have hn := hs.ok.nargs
  have ha := Lay.argOff_lt (L := L) (j := j) (by omega)
  have e : arg j = Impl.RsaPkcs1Sig.Arm.argOff L.F j := by rw [hg.F]
  rw [e]
  exact ⟨hs.ok.addrB (by omega), by rw [hs.rd, hs.wr]; exact hs.ok.arg_read hj, hs.arg hj⟩

/-- The label's hash. -/
theorem label_vp (hg : Geo L scr) (h : OHash) {j o ll : Nat} {lab : BitVec 32} (hj : j + 1 < L.argv.length)
    (hj4 : arg (j + 1) < 4096) (hj4' : arg j < 4096)
    (hlab : L.argv.getD j 0 = lab) (hll : L.argv.getD (j + 1) 0 = BitVec.ofNat 32 ll)
    (hb : RBuf L lab ll) (dS : Region.Disjoint ⟨State.addr lab, ll⟩ (sR scr oSt h.H.S))
    (dW : Region.Disjoint ⟨State.addr lab, ll⟩ (sR scr oW h.ok.Wb))
    (dL : Region.Disjoint ⟨State.addr lab, ll⟩ L.LOW)
    (ho1 : oSt + 256 ≤ o) (ho2 : o + 64 ≤ oW) {labB : State → List Byte}
    (hbytes : ∀ σ s, Ctx L scr σ s → Spec.Sha256.bytesAt s.mem (State.addr lab) ll = labB σ)
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem)
      (hashLabel h.H j o)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < h.H.D, s.mem (sa scr (o + i)) = (h.G.hash (labB σ)).getD i 0) := by
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.DF
  have hll32 : ll < 2 ^ 32 := hb.n32
  have ofr : ∀ m m', Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW] m m' →
      Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' :=
    fun _ _ f => f.mono (by simp)
  show VP _ (.seq (.block initArgs) (.seq (.call h.H.initN h.H.initC) (.seq (.block (updLabArgs j)) (.seq (updCall h.H)
    (.seq (.block (finLabArgs j o)) (.seq (.block toR12) (finCall h.H))))))) _
  refine VP.assoc (VP.seq (init_vp hg h.H h.ok (Inv := Inv) fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))) ?_)
  -- `update`'s arguments.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (State.addr lab) ll = labB σ ∧
      UArgs scr lab ll 0 s)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, rp⟩ => ?_) ?_
  · obtain ⟨a1, r1, v1⟩ := argG hg hc.st (j := j) (by omega)
    obtain ⟨a2, r2, v2⟩ := argG hg hc.st (j := j + 1) hj
    rw [hlab] at v1
    rw [hll] at v2
    have hw : WP isa (.block (updLabArgs j)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        UArgs scr lab ll 0 t := by
      prun [updLabArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a1, r1, v1, a2, r2, v2, hj4, hj4',
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide)]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ =>
      ⟨hc.regs rd wr sp m, m ▸ hi, m ▸ rp, rfl, hbytes σ t (hc.regs rd wr sp m), u⟩
  refine VP.seq (upd_vp hg h.H h.ok (msg := fun _ => []) (dat := labB) (c := 0) (Inv := Inv) hb dS dW dL (by decide)
    fun σ m m' hm hf => hI σ m m' hm (ofr _ _ hf)) ?_
  -- `finalize`'s arguments.
  refine VP.seq (F := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ))
    (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
      h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ)) ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
      s.gpr .r1 = scr + BitVec.ofNat 32 o ∧ s.gpr .r10 = scr + BitVec.ofNat 32 oW ∧
      s.gpr .r2 = BitVec.ofNat 32 ll ∧ s.gpr .r3 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, rp⟩ => ?_) ?_
  · obtain ⟨a2, r2, v2⟩ := argG hg hc.st (j := j + 1) hj
    rw [hll] at v2
    have hw : WP isa (.block (finLabArgs j o)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 o ∧
        t.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ t.gpr .r2 = BitVec.ofNat 32 ll ∧ t.gpr .r3 = 0 := by
      prun [finLabArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a2, r2, v2, hj4,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
        movw_val (show o < 2 ^ 16 by oomega)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, r10, r2, r3⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hi, m ▸ rp⟩, r0, r1,
      r10, r2, r3⟩
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s)
    ((toR12_vp (fun σ s hh => hh.2.2.2.1) fun σ s v hh => ?_).mono (fun _ _ hh => hh)
    fun σ s ⟨⟨⟨hc, hi, rp⟩, r0, r1, _, r2, r3⟩, r12⟩ => ⟨hc, hi, rp, by rw [List.nil_append, ← hbytes σ s hc,
      Spec.Sha256.bytesAt, List.length_map, List.length_range], r0, r1, r12, r2, r3⟩) ?_
  · obtain ⟨⟨hc, hi, rp⟩, r0, r1, r10, r2, r3⟩ := hh
    have e : ∀ r, r ≠ .r12 → (s.setReg .r12 v).gpr r = s.gpr r := fun r hr => by
      simp only [VG.Arm.RegUpd.gpr_setReg, hr, ite_false]
    exact ⟨⟨Ctx.setReg_iff.mpr hc, hi, rp⟩, by rw [e _ (by decide), r0], by rw [e _ (by decide), r1],
      by rw [e _ (by decide), r10], by rw [e _ (by decide), r2], by rw [e _ (by decide), r3]⟩
  refine (fin_vp hg h.H h.ok (o := o) (c := ll) (msg := fun σ => [] ++ labB σ) (Inv := Inv) (.inr (by omega))
    (.inl (by omega)) (by oomega) hll32 fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))).mono
    (fun _ _ hh => hh) fun σ s ⟨hc, hi, hd⟩ => ⟨hc, hi, fun i hi' => ?_⟩
  have e := congrArg (fun l => l.getD i 0) hd
  simp only [List.nil_append] at e
  rw [h.hash, ← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi', Spec.Sha256.bytesAt,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.RsaOaep.Arm
