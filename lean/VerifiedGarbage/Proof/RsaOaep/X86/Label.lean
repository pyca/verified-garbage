module

import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
public import VerifiedGarbage.Proof.RsaOaep.X86.Base

/-!
# RSAES-OAEP on x86: the label's hash

`label_vp`: with the label in the arguments `j` (its address) and `j + 1`
(its length), a range of bytes the body may read whose bytes do not change,
`hashLabel` writes `H(label)` to `scratch + o`, as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oDig oEm oRsa frameBytes arg)
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable {L : Lay} {scr : BitVec 32}

/-- The label's hash. -/
theorem label_vp (hg : Geo L scr) (h : OHash) {j o ll : Nat} {lab : BitVec 32} (hj : j + 1 < L.argv.length)
    (ht : TaintOk [.esp, .ebp] (.block (updLabArgs j))) (ht' : TaintOk [.esp, .ebp] (.block (finLabArgs j o)))
    (hlab : L.argv.getD j 0 = lab) (hll : L.argv.getD (j + 1) 0 = BitVec.ofNat 32 ll)
    (hb : RBuf L lab ll) (dS : Region.Disjoint ⟨lab.setWidth 64, ll⟩ (sR scr oSt h.H.S))
    (dW : Region.Disjoint ⟨lab.setWidth 64, ll⟩ (sR scr oCW h.ok.Wb))
    (dL : Region.Disjoint ⟨lab.setWidth 64, ll⟩ L.LOW)
    (ho1 : oSt + 256 ≤ o) (ho2 : o + 64 ≤ oEm) {labB : State → List Byte}
    (hbytes : ∀ σ s, Ctx L scr σ s → Spec.Sha256.bytesAt s.mem (lab.setWidth 64) ll = labB σ)
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem)
      (hashLabel h.H j o)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < h.H.D, s.mem (sa scr (o + i)) = (h.G.hash (labB σ)).getD i 0) := by
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.DF
  have hll32 : ll < 2 ^ 32 := hb.n32
  have ofr : ∀ m m', Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW] m m' →
      Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' :=
    fun _ _ f => f.mono (by simp)
  show VP _ (.seq (.block initArgs) (.seq (callInit h.H) (.seq (.block (updLabArgs j)) (.seq (callUpd h.H)
    (.seq (.block (finLabArgs j o)) (callFin h.H)))))) _
  refine vpAssoc (VP.seq (init_vp hg h.H h.ok (Inv := Inv) fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))) ?_)
  -- `update`'s arguments.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (lab.setWidth 64) ll = labB σ ∧
      UArgs scr lab ll 0 s)
    (VP.taint [.esp, .ebp] ht (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, rp⟩ => ?_) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => ?_
    have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
      (by decide) (by decide)).upd u4 (by decide) (by decide)
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine c4.wp_arg hg (by omega) (by decide) (by decide) fun t5 c5 u5 =>
      c5.wp_arg hg hj (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, m4]
    refine ⟨c6, m6 ▸ hi, m6 ▸ rp, rfl, hbytes σ t6 c6, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · rw [u6.other _ (by decide), u5.gpr, hlab]
    · rw [u6.gpr, hll]
  refine VP.seq (upd_vp hg h.H h.ok (msg := fun _ => []) (dat := labB) (c := 0) (Inv := Inv) hb dS dW dL (by decide)
    fun σ m m' hm hf => hI σ m m' hm (ofr _ _ hf)) ?_
  -- `finalize`'s arguments.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s)
    (VP.taint [.esp, .ebp] ht' (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, rp⟩ => ?_) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg hj (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => ?_
    refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => WP.block_nil ?_
    have c6 : Ctx L scr σ t6 := (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
      (by decide) (by decide))
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨c6, m6 ▸ hi, m6 ▸ rp, by rw [List.nil_append, ← hbytes σ s hc, Spec.Sha256.bytesAt, List.length_map,
      List.length_range], ⟨?_, ?_, ?_, ?_⟩⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hll]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · simp (disch := decide) only [u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
  refine (fin_vp hg h.H h.ok (o := o) (c := ll) (msg := fun σ => [] ++ labB σ) (Inv := Inv) (.inr (by omega))
    (by oomega) (by oomega) hll32 fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))).mono
    (fun _ _ hh => hh) fun σ s ⟨hc, hi, hd⟩ => ⟨hc, hi, fun i hi' => ?_⟩
  have e := congrArg (fun l => l.getD i 0) hd
  simp only [List.nil_append] at e
  rw [h.hash, ← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi', Spec.Sha256.bytesAt,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.RsaOaep.X86
