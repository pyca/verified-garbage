module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import Batteries.Tactic.Trans
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Dsa.AArch64.Generation.ContextSeed`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.Generation.SeedArguments`, which this module and modules that import it used -/

section

/-! # Bind each complete seed to q hashing without resetting witness consumption -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def seedWords (W : Nat → BitVec 64) (len : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (VG.Proof.Bignum.off (W 5) q)) 25 (W 1)) 26 (BitVec.ofNat 64 len)

theorem seedArguments_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hl : len < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments len)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (seedWords W len) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have cast : (BitVec.ofNat 16 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hl]
  have read : (s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)).readW (VG.Proof.Bignum.off F 8) 64 = W 1 := by
    change VG.Proof.Bignum.word (s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)) F 8 = W 1
    rw [(VG.Proof.Bignum.writeW_outside _ F _ (d := 0) (by decide)).word
      (d := 8) (Or.inr (by decide)) (by decide)]
    exact R.fr 1 (by decide)
  simp only [VG.Proof.Bignum.off, BitVec.add_zero] at read
  have st0 : InRegions s.wr F 8 := by simpa [VG.Proof.Bignum.off] using L.st (d := 0) (n := 8) (by decide)
  have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  have hq : (BitVec.ofNat 16 q).setWidth 64 = BitVec.ofNat 64 q := by decide
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      t.mem = ((s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)).writeW (VG.Proof.Bignum.off F 200) (W 1)).writeW
        (VG.Proof.Bignum.off F 208) (BitVec.ofNat 64 len)) (by
    brun [State.write, Impl.Dsa.AArch64.Generation.seedArguments, sLab, sLabLen,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 8) (by decide),
      exec_storeSp (off := 0) (by decide), exec_storeSp (off := 200) (by decide),
      exec_storeSp (off := 208) (by decide), L.sp, BitVec.add_zero,
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 8) (n := 8) (by decide),
      st0, L.st (d := 200) (n := 8) (by decide), L.st (d := 208) (n := 8) (by decide),
      hw, hq, cast, read, VG.Proof.Bignum.off]) rfl rfl rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (seedWords W len) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) _).wf L.geo (by decide : 25 < nW) _).wf L.geo (by decide : 26 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [seedWords, upd]) kt.sp kt.wr, Rt, ?_, kt⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ F _ (d := 200) (by decide)).mono (by decide) (by decide))).trans
      ((writeW_outside _ F _ (d := 208) (by decide)).mono (by decide) (by decide))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega_using [hn]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Prepare q hashing while retaining all persistent search inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem prepareSeed_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments p.geo.qLen)) s fun t =>
      GenerationMemory p (seedWords W p.geo.qLen) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (seedArguments_ok h.layout R (by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff := GenerationContext.frame_single (p := p) ft
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr, ff, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | simpa [seedWords, upd] using ((h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot).symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.QCandidate`, which only this module used -/

section

/-! Hashing and shaping construct q while retaining the complete caller frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64 VG.Proof.Pbkdf2.Md.AArch64
open VG.Proof.Ffdh.ParameterCandidate

theorem qCandidate_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp qp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hp : W 0 = qp)
    (hqw : ∀ i < len, InRegions s.wr (VG.Proof.Bignum.off qp i) 1)
    (dFQ : Region.Disjoint ⟨F, frameBytes⟩ ⟨qp, len⟩)
    (dSQ : Region.Disjoint ⟨S, oRsa⟩ ⟨qp, len⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.qCandidate G1 G256) s fun t =>
      Lay t F S ∧ Step F S [⟨qp, len⟩] s t ∧
      Frame [⟨S, oRsa⟩, ⟨qp, len⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem qp len = shapedOctets
        (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)) 7 := by
  unfold Impl.Dsa.AArch64.Generation.qCandidate
  refine WP.seq (WP.mono (seedHash_frame_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A)
    fun u ⟨Lu, step, huf, V', Ru, _, hdigest⟩ => ?_)
  refine WP.seq (WP.mono (qArgs_ok Lu Ru hp A.hll) fun v ⟨hv2, hv12, hv9, hvm, kv⟩ => ?_)
  have bslen : (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).length = len := by
    rw [← hdigest, bytesAt_length]
  have Lv : Lay v F S := Lu.congr kv.sp kv.wr (by rw [hvm])
  have Rv : Rep v.mem F S V' W := hvm ▸ Ru
  have hread : ∀ i < len, InRegions (v.rd ++ v.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i) 1 := by
    intro i hi
    rw [kv.rd, kv.wr, VG.Proof.Bignum.off_off]
    exact Lu.sld (o := oDig + i) (n := 1) (by rcases hlen with rfl | rfl <;> simp only [oDig, oRsa] <;> omega_using [hi])
  have hwrite : ∀ i < len, InRegions v.wr (VG.Proof.Bignum.off qp i) 1 := by
    intro i hi; rw [kv.wr, step.wr]; exact hqw i hi
  have hsep : ∀ i < len, ∀ j < len, VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i ≠ VG.Proof.Bignum.off qp j := by
    intro i hi j hj he
    apply dSQ (VG.Proof.Bignum.off qp j)
    · rw [← he, VG.Proof.Bignum.off_off]
      exact cS S (o := oDig + i) (n := 1) (by rcases hlen with rfl | rfl <;> simp only [oDig, oRsa] <;> omega_using [hi])
    · exact Offset.contains_base qp (by omega_using [hj]) (by rcases hlen with rfl | rfl <;> omega_using [hj])
  have hbytes : ∀ i < len, v.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i) =
      (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).getD i 0 := by
    intro i hi
    have hh := congrArg (fun xs : List Byte => xs.getD i 0) hdigest
    simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi, VG.Proof.Bignum.off, hvm] using hh
  have hshape := qShape_ok (bs := Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len))
    (by rw [bslen]; rcases hlen with rfl | rfl <;> omega_using [])
    (by rw [bslen]; rcases hlen with rfl | rfl <;> omega_using [])
    hv12 hv2 (by rw [bslen]; exact hv9) (by rw [bslen]; exact hread)
    (by rw [bslen]; exact hwrite) (by rw [bslen]; exact hbytes) (by rw [bslen]; exact hsep)
  rw [bslen] at hshape
  refine WP.mono hshape fun t ⟨hq, hf, kt⟩ => ?_
  have hwords : ∀ d, d + 8 ≤ frameBytes → VG.Proof.Bignum.word t.mem F d = VG.Proof.Bignum.word v.mem F d :=
    words_outside_bytes (by decide) hf (fun i hi =>
      out_scr dFQ.symm (Offset.contains_base qp (by omega_using [hi]) (by rcases hlen with rfl | rfl <;> omega_using [hi])))
  have Lt : Lay t F S := Lv.congr kt.sp kt.wr (hwords sScr (by decide))
  have qframe : Frame [⟨qp, len⟩] v.mem t.mem := by
    intro a ha
    apply hf
    intro i hi he
    apply ha ⟨qp, len⟩ (by simp)
    rw [he]
    exact Offset.contains_base qp (by omega_using [hi]) (by rcases hlen with rfl | rfl <;> omega_using [hi])
  have hfinal : Frame [⟨S, oRsa⟩, ⟨qp, len⟩, retR F] s.mem t.mem := by
    have hvf : Frame [⟨S, oRsa⟩, retR F] s.mem v.mem := by rw [hvm]; exact huf
    exact (hvf.mono (by simp)).trans (qframe.mono (by simp))
  have k := kv.trans kt
  refine ⟨Lt, ⟨k.rd.trans step.rd, k.wr.trans step.wr, k.sp.trans step.sp, ?_,
    step.vec.trans k.vcs, hfinal.mono (by simp)⟩, hfinal, ⟨fun o => t.mem (VG.Proof.Bignum.off S o), ?_⟩, hq⟩
  · intro r hr h30
    trans u.gpr r
    · apply k.gpr r
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · exact step.cs r hr h30
  · exact ⟨fun _ _ => rfl, fun k hk => (hwords (8 * k) (by unfold nW at hk; omega_using [hk])).trans (Rv.fr k hk)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! The native digest shaper emits the exact fixed-width encoding of q. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem qBuild_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp op : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hop : W 0 = op)
    (hout : ∀ i < len, InRegions s.wr (off op i) 1)
    (hframe : Region.Disjoint ⟨F, frameBytes⟩ ⟨op, len⟩)
    (hscratch : Region.Disjoint ⟨S, oRsa⟩ ⟨op, len⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.qCandidate G1 G256) s fun t =>
      Spec.Rsa.bytesAt t.mem op len =
        Spec.Dsa.encodeBE len (Spec.Dsa.qCandidate (8 * len) (Spec.Rsa.bytesAt s.mem rp len)) ∧
      Step F S [⟨op, len⟩] s t ∧ Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      Lay t F S ∧ ∃ V', Rep t.mem F S V' W := by
  refine WP.mono (qCandidate_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A hop
    hout hframe hscratch) fun t ⟨Lt, step, hf, Rt, hb⟩ => ?_
  have hhash : (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).length = len := by
    rcases hlen with rfl | rfl
    · simpa only [Nat.reduceMul, Spec.Dsa.seedHash, Spec.Mgf1.sha1, beq_self_eq_true, ite_true] using (hs1 _).trans hd1
    · simpa only [Nat.reduceMul, Spec.Dsa.seedHash, Spec.Mgf1.sha256, show (256 == 160) = false from rfl,
        Bool.false_eq_true, ite_false] using (hs256 _).trans hd256
  have he := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op len)
  rw [VG.Proof.Bignum.bytesAt_length, hb,
    VG.Proof.Dsa.Generation.qCandidate_octets (by rcases hlen with rfl | rfl <;> omega_using [])
      _ (by rw [hhash])] at he
  exact ⟨hb.trans he.symm, step, hf.mono (by simp), Lt, Rt⟩

end VG.Proof.Dsa.AArch64.Generation
