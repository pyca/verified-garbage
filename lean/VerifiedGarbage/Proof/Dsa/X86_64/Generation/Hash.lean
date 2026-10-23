module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
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

/-- The hash helper's exact byte result, retaining its frame and scratch facts. -/
theorem hash_bytes_frame {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D) {s : State} {F S rp : Addr} {len : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (hashLabel G oDig) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) G.D = Hs.hash (Spec.Rsa.bytesAt s.mem rp len) := by
  refine WP.mono (hashLabel_frame_ok hG hHh L R A (Or.inl rfl))
    fun t ⟨Lt, hrd, hwr, hcs, hframe, V', Rt, hf, hb⟩ => ?_
  refine ⟨Lt, hrd, hwr, hcs, hframe, V', Rt, hf, ?_⟩
  have hd : G.D ≤ 64 := by
    have hh := hG.hDF
    have hh' := hG.hF
    omega
  apply List.ext_getElem
  · rw [bytesAt_length, hsize]
  · intro i hi hi'
    have hiD : i < G.D := by simpa only [bytesAt_length] using hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    change t.mem (off S oDig + BitVec.ofNat 64 i) = _
    rw [show off S oDig + BitVec.ofNat 64 i = off S (oDig + i) by simp [off, BitVec.ofNat_add, BitVec.add_assoc],
      Rt.scr _ (by unfold oDig oRsa; omega), hb i hiD]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rfl

theorem hash_bytes {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D) {s : State} {F S rp : Addr} {len : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (hashLabel G oDig) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) G.D = Hs.hash (Spec.Rsa.bytesAt s.mem rp len) := by
  exact WP.mono (hash_bytes_frame hG hHh hsize L R A)
    fun _ ⟨Lt, rd, wr, cs, _, rest⟩ => ⟨Lt, rd, wr, cs, rest⟩

/-- Dispatch is determined by the public seed width. -/
theorem hashTest_ok {s : State} {F S : Addr} (L : Lay s F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    {len : Nat} (hll : W 28 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.X86_64.Generation.hashTest) s fun t =>
      t.zf = some (BitVec.ofNat 64 len == 20) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (BitVec.ofNat 64 len == 20) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩
  xrun [Impl.Dsa.X86_64.Generation.hashTest, ea_sp, L.rsp,
    L.ld (d := sLabLen) (by decide), R.slot (d := sLabLen) (k := 28) rfl (by decide) hll]
  exact sub_beq_zero (BitVec.ofNat 64 len) 20

/-- SHA selection, hashing, and preservation for a supported DSA seed width. -/
theorem seedHash_frame_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (Impl.Dsa.X86_64.Generation.seedHash G1 G256) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) len =
          Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len) := by
  unfold Impl.Dsa.X86_64.Generation.seedHash
  refine WP.seq (WP.mono (hashTest_ok L R A.hll) fun u ⟨hz, hm, hk⟩ => ?_)
  have Lu : Lay u F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Au : LabAt u F S W rp len := A.congr hk.2.1 hk.2.2 rfl rfl
  have hcs : ∀ r ∈ calleeSaved, u.gpr r = s.gpr r := by
    intro r hr
    exact hk.gpr (by intro h; simp only [List.mem_singleton] at h; subst r; simp [calleeSaved] at hr)
  rcases hlen with rfl | rfl
  · refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (hash_bytes_frame h1 he1 hs1 Lu Ru Au) fun t ⟨Lt, rd, wr, cs, hframe, V', Rt, hf, hb⟩ => ?_
    refine ⟨Lt, rd.trans hk.2.1, wr.trans hk.2.2, fun r hr => (cs r hr).trans (hcs r hr), (by simpa only [hm] using hframe), V', Rt, hf, ?_⟩
    simpa only [hd1, hm, Spec.Dsa.seedHash, Nat.reduceMul, beq_self_eq_true, ite_true, Spec.Mgf1.sha1] using hb
  · refine WP.ite false (by simp [eval, hz]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.mono (hash_bytes_frame h256 he256 hs256 Lu Ru Au) fun t ⟨Lt, rd, wr, cs, hframe, V', Rt, hf, hb⟩ => ?_
    refine ⟨Lt, rd.trans hk.2.1, wr.trans hk.2.2, fun r hr => (cs r hr).trans (hcs r hr), (by simpa only [hm] using hframe), V', Rt, hf, ?_⟩
    simpa only [hd256, hm, Spec.Dsa.seedHash, Nat.reduceMul, show (256 == 160) = false from rfl,
      Bool.false_eq_true, ite_false, Spec.Mgf1.sha256] using hb

theorem seedHashAt_frame_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (Impl.Dsa.X86_64.Generation.seedHashAt G1 G256 len) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) len =
          Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len) := by
  rcases hlen with rfl | rfl
  · simp only [Impl.Dsa.X86_64.Generation.seedHashAt, ite_true]
    refine WP.mono (hash_bytes_frame h1 he1 hs1 L R A) fun t ⟨Lt, rd, wr, cs, hf, V', Rt, hv, hb⟩ => ?_
    refine ⟨Lt, rd, wr, cs, hf, V', Rt, hv, ?_⟩
    simpa only [hd1, Spec.Dsa.seedHash, Nat.reduceMul, beq_self_eq_true, ite_true, Spec.Mgf1.sha1] using hb
  · simp only [Impl.Dsa.X86_64.Generation.seedHashAt, show (32 = 20) = False from propext (by decide), ite_false]
    refine WP.mono (hash_bytes_frame h256 he256 hs256 L R A) fun t ⟨Lt, rd, wr, cs, hf, V', Rt, hv, hb⟩ => ?_
    refine ⟨Lt, rd, wr, cs, hf, V', Rt, hv, ?_⟩
    simpa only [hd256, Spec.Dsa.seedHash, Nat.reduceMul, show (256 == 160) = false from rfl,
      Bool.false_eq_true, ite_false, Spec.Mgf1.sha256] using hb

theorem seedHash_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (Impl.Dsa.X86_64.Generation.seedHash G1 G256) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) len =
          Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len) := by
  exact WP.mono (seedHash_frame_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A)
    fun _ ⟨Lt, rd, wr, cs, _, rest⟩ => ⟨Lt, rd, wr, cs, rest⟩

end VG.Proof.Dsa.X86_64.Generation
