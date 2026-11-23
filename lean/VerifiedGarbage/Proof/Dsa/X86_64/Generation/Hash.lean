module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ViaSlot
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # The streaming seed hash equals DSA's selected SHA-1 or SHA-256 -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.Pbkdf2.Md.X86_64

/-- Frame words 29 and 30 hold the addresses of `G`'s `update` and
`finalize` (`hashLabelI`). -/
def HashSlots (G : Impl.Pbkdf2.Md.X86_64.Stream) (W : Nat → BitVec 64) (s : State) : Prop :=
  W 29 = s.syms G.updN ∧ W 30 = s.syms G.finN

theorem HashSlots.congr {G : Impl.Pbkdf2.Md.X86_64.Stream} {W : Nat → BitVec 64} {s t : State}
    (h : HashSlots G W s) (hy : t.syms = s.syms) : HashSlots G W t :=
  ⟨by rw [hy]; exact h.1, by rw [hy]; exact h.2⟩

/-- `hashLabel_frame_ok` of `hashLabelI`: with the addresses of `update` and
`finalize` in frame words 29 and 30. -/
theorem hashLabelI_frame_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {lab : Addr} {labLen : Nat}
    (A : LabAt u F S W lab labLen) (hU : W 29 = u.syms G.updN) (hF : W 30 = u.syms G.finN) :
    WP isa (Impl.Dsa.X86_64.Generation.hashLabelI G oDig) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] u.mem u'.mem ∧
      ∃ V', Rep u'.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        ∀ i < G.D, V' (oDig + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ oDig ∧ oDig + 64 ≤ oW := by decide
  have hlen := A.len
  unfold Impl.Dsa.X86_64.Generation.hashLabelI Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs
    Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs
  refine WP.seq (WP.mono_syms (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide))
    fun u1 ⟨hdi1, hm1, k1⟩ y1 => ?_)
  have L1 : Lay u1 F S := L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono_syms (init_ok hG L1 R1 hdi1) fun u2 ⟨L2, rd2, wr2, cs2, R2, hF2, hr2⟩ y2 => ?_)
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  have A2 : LabAt u2 F S W lab labLen := A.congr (rd2.trans k1.2.1) (wr2.trans k1.2.2) rfl rfl
  refine WP.seq (WP.mono_syms (labA_ok L2 R2 A2) fun u3 ⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩ y3 => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W := hm3 ▸ R2
  have A3 : LabAt u3 F S W lab labLen := A2.congr k3.2.1 k3.2.2 rfl rfl
  have sy3 : u3.syms = u.syms := y3.trans (y2.trans y1)
  have hw3 : word u3.mem F Impl.Dsa.X86_64.Generation.updSlot = u3.syms G.updN := by
    rw [sy3, ← hU]; exact R3.fr 29 (by decide)
  have g3 : ∀ {r : Reg}, r ≠ .rax → (slotState u3 G.updN).gpr r = u3.gpr r := slotState_gpr u3 G.updN
  refine WP.seq (viaSlot_ok L3 (by decide) hw3 (WP.mono_syms (updExt_ok hG (lay_slotState L3 G.updN)
    (RegUpd.mem_setReg u3 .rax (u3.syms G.updN) ▸ R3) A3.len (by rw [RegUpd.rd_setReg, RegUpd.wr_setReg]; exact A3.cov)
    A3.dS A3.dK ((g3 (by decide)).trans hdi3) ((g3 (by decide)).trans hdx3)
    ((g3 (by decide)).trans hcx3) ((g3 (by decide)).trans h83))
    fun u4 ⟨L4, rd4, wr4, cs4, R4, hF4, hr4⟩ y4 => ?_))
  have hR4 := hr4 [] (by rw [RegUpd.mem_setReg]; exact hm3 ▸ hr2) (by rw [g3 (by decide), hsi3]; rfl)
  rw [List.nil_append, RegUpd.mem_setReg, hm3] at hR4
  obtain ⟨V4, R4, hV4, -⟩ := Rep.ex R4
  refine WP.seq (WP.mono_syms (labF_ok L4 R4 A.hll (o := oDig) (by decide))
    fun u5 ⟨hdi5, hsi5, hdx5, hcx5, hm5, k5⟩ y5 => ?_)
  have L5 : Lay u5 F S := L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5])
  have R5 : Rep u5.mem F S V4 W := hm5 ▸ R4
  have sy5 : u5.syms = u.syms := y5.trans (y4.trans ((setReg_syms _ _ _).trans sy3))
  have hw5 : word u5.mem F Impl.Dsa.X86_64.Generation.finSlot = u5.syms G.finN := by
    rw [sy5, ← hF]; exact R5.fr 30 (by decide)
  have g5 : ∀ {r : Reg}, r ≠ .rax → (slotState u5 G.finN).gpr r = u5.gpr r := slotState_gpr u5 G.finN
  refine viaSlot_ok L5 (by decide) hw5 (WP.mono (fin_frame_ok hG (lay_slotState L5 G.finN)
    (RegUpd.mem_setReg u5 .rax (u5.syms G.finN) ▸ R5) (o := oDig) (Or.inr hoo) ((g5 (by decide)).trans hdi5)
    ((g5 (by decide)).trans hdx5) ((g5 (by decide)).trans hcx5))
    fun u6 ⟨L6, rd6, wr6, cs6, R6, hF6, hr6⟩ => ?_)
  have hlb : (Spec.Rsa.bytesAt u2.mem lab labLen).length = labLen := by
    simp [Spec.Rsa.bytesAt]
  have hdig := hr6 _ (by rw [RegUpd.mem_setReg]; exact hm5 ▸ hR4) (by rw [hlb]; omega_using [hlen])
    (by rw [g5 (by decide), hsi5, hlb])
  have hlab : Spec.Rsa.bytesAt u2.mem lab labLen = Spec.Rsa.bytesAt u.mem lab labLen := by
    rw [← hm1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hF2.bytes (R := ⟨lab, labLen⟩) (fun r hr => ?_)
      (by show labLen ≤ 2 ^ 64; omega_using [hlen]) (List.mem_range.mp hi)
    rcases List.mem_append.mp hr with hr | hr
    · simp only [regs, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega_using [hzS]
      have hs : Region.Sub ⟨off S oSt, G.S⟩ ⟨S, oRsa⟩ := Offset.sub_base S h1
      exact A.dS.sub_right hs
    · rw [List.mem_singleton.mp hr]; exact A.dK.symm
  obtain ⟨V6, R6, hV6, hV6'⟩ := Rep.ex R6
  have frame2 := hash_frame_large (by
    simp only [List.mem_singleton]
    rintro r rfl
    unfold oSt oRsa
    omega) hF2
  have frame4 := hash_frame_large (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> dsimp only [oSt, oW, oRsa] <;> omega_arith) hF4
  have frame6 := hash_frame_large (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · unfold oSt oRsa; omega
    · dsimp only [oDig, oRsa]; omega_using [hzF]
    · unfold oW oRsa; omega) hF6
  rw [hm1] at frame2
  rw [RegUpd.mem_setReg, hm3] at frame4
  rw [RegUpd.mem_setReg, hm5] at frame6
  refine ⟨L6, rd6.trans (k5.2.1.trans (rd4.trans (k3.2.1.trans (rd2.trans k1.2.1)))),
    wr6.trans (k5.2.2.trans (wr4.trans (k3.2.2.trans (wr2.trans k1.2.2)))), fun r hr => ?_,
    (frame2.trans frame4).trans frame6, V6, R6, fun x hx => ?_, fun i hi => ?_⟩
  · have hne : r ≠ .rax := fun h => by subst h; simp [calleeSaved] at hr
    rw [cs6 r hr, g5 hne, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr, g3 hne,
      keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · simp only [labR, inR_cons, inR_nil, or_false] at hx
    rw [hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzF, hzW, hx]),
      hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, hx]),
      hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hx])]
  · rw [hV6' _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzDF, hi]), hdig i hi, hHh, hlab]

/-- The hash helper's exact byte result, retaining its frame and scratch facts. -/
theorem hash_bytes_frame {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D) {s : State} {F S rp : Addr} {len : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hU : W 29 = s.syms G.updN)
    (hF : W 30 = s.syms G.finN) :
    WP isa (Impl.Dsa.X86_64.Generation.hashLabelI G oDig) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) G.D = Hs.hash (Spec.Rsa.bytesAt s.mem rp len) := by
  refine WP.mono (hashLabelI_frame_ok hG hHh L R A hU hF)
    fun t ⟨Lt, hrd, hwr, hcs, hframe, V', Rt, hf, hb⟩ => ?_
  refine ⟨Lt, hrd, hwr, hcs, hframe, V', Rt, hf, ?_⟩
  have hd : G.D ≤ 64 := by
    have hh := hG.hDF
    have hh' := hG.hF
    omega_using [hh, hh']
  apply List.ext_getElem
  · rw [bytesAt_length, hsize]
  · intro i hi hi'
    have hiD : i < G.D := by simpa only [bytesAt_length] using hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    change t.mem (off S oDig + BitVec.ofNat 64 i) = _
    rw [show off S oDig + BitVec.ofNat 64 i = off S (oDig + i) by simp [off, BitVec.ofNat_add, BitVec.add_assoc],
      Rt.scr _ (by unfold oDig oRsa; omega_using [hd, hiD]), hb i hiD]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rfl

theorem seedHashAt_frame_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len)
    (hU : W 29 = s.syms (if len = 20 then G1 else G256).updN)
    (hF : W 30 = s.syms (if len = 20 then G1 else G256).finN) :
    WP isa (Impl.Dsa.X86_64.Generation.seedHashAt G1 G256 len) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) len =
          Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len) := by
  rcases hlen with rfl | rfl
  · simp only [Impl.Dsa.X86_64.Generation.seedHashAt, ite_true]
    simp only [↓reduceIte] at hU hF
    refine WP.mono (hash_bytes_frame h1 he1 hs1 L R A hU hF) fun t ⟨Lt, rd, wr, cs, hf, V', Rt, hv, hb⟩ => ?_
    refine ⟨Lt, rd, wr, cs, hf, V', Rt, hv, ?_⟩
    simpa only [hd1, Spec.Dsa.seedHash, Nat.reduceMul, beq_self_eq_true, ite_true, Spec.Mgf1.sha1] using hb
  · simp only [Impl.Dsa.X86_64.Generation.seedHashAt, show (32 = 20) = False from propext (by decide), ite_false]
    simp only [show (32 = 20) = False from propext (by decide), ite_false] at hU hF
    refine WP.mono (hash_bytes_frame h256 he256 hs256 L R A hU hF) fun t ⟨Lt, rd, wr, cs, hf, V', Rt, hv, hb⟩ => ?_
    refine ⟨Lt, rd, wr, cs, hf, V', Rt, hv, ?_⟩
    simpa only [hd256, Spec.Dsa.seedHash, Nat.reduceMul, show (256 == 160) = false from rfl,
      Bool.false_eq_true, ite_false, Spec.Mgf1.sha256] using hb

end VG.Proof.Dsa.X86_64.Generation
