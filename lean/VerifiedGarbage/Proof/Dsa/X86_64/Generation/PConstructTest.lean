module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFull
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmall
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets

/-! # A p candidate is constructed and tested entirely by verified native code -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.Generation.Layout

def PConstructTestEnd (p : PPrimalityPlan) (used : Nat) (s t : State) : Prop :=
  ∃ (used' : Nat) (status : BitVec 64) (V : Nat → Byte),
    used' ≤ p.rand.length ∧ Lay t p.construct.hash.F p.construct.hash.S ∧
    Rep t.mem p.construct.hash.F p.construct.hash.S V
      (upd (upd p.construct.hash.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
    Spec.Rsa.bytesAt t.mem (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len =
      Spec.Dsa.encodeBE p.construct.len p.construct.value ∧
    Spec.Rsa.bytesAt t.mem (off (p.construct.hash.W 5) exponent) p.construct.len =
      Spec.Dsa.encodeBE p.construct.len ((p.construct.value - 1) / Spec.Rsa.os2ip p.construct.qb) ∧
    (p.result used = none → status = BitVec.ofNat 64 0) ∧
    (∀ b rest, p.result used = some (b, rest) →
      status = BitVec.ofNat 64 (if b then 1 else 3) ∧ used' = p.rand.length - rest.length) ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem pConstructTest_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D) (M : Mont) (K : Kernel)
    {p : PPrimalityPlan} (hd : G.D = p.construct.hash.len) {s : State}
    (hs : PConstructState p.construct H s)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.construct.hash.len) bs).length = 8 * p.construct.hash.len)
    {used : Nat} (hused : p.construct.hash.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.length)
    (htape : Src s p.construct.B p.construct.Z p.rp p.rand)
    (hwitness : ∀ i < p.construct.len, InRegions s.wr (off (off (p.construct.hash.W 5) witness) i) 1) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.pConstruct G p.construct.len p.construct.hash.len)
      (Impl.Dsa.X86_64.Generation.pTest M.mm K.run p.construct.len)) s (PConstructTestEnd p used s) := by
  refine WP.seq (WP.mono (pConstruct_ok hG hHh hsize hd hs hhash hseedsize)
    fun u ⟨up, ue, ho, hb, Lu, ⟨Vu, Ru⟩, wu, hp, fu, rdu, wru⟩ => ?_)
  have hlen : 0 < p.construct.len ∧ p.construct.len < 2 ^ 64 := by
    rcases p.construct.width with hh | hh | hh <;> omega
  have hbound : p.construct.value < 256 ^ p.construct.len := by
    simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb
  have hread : InRegions (u.rd ++ u.wr) (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) 1 := by
    obtain ⟨r, hr, hc⟩ := hs.pWrite 0 hlen.1
    rw [rdu, wru]
    exact ⟨r, List.mem_append_right _ hr, by simpa [off] using hc⟩
  by_cases hsmall : p.construct.value < 2 ^ (8 * p.construct.len - 1)
  · refine WP.mono (pTest_small_ok M.mm K.run Lu Ru wu hp hlen.1 hbound up hread hsmall)
      fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    have ff : Frame p.testWrites u.mem t.mem := by
      intro a ha
      apply ft a
      right
      have hn := ha ⟨p.construct.hash.F, frameBytes⟩ (by simp [PPrimalityPlan.testWrites])
      change ¬ ofs p.construct.hash.F a < frameBytes at hn
      unfold frameBytes at hn
      omega
    have hself : upd p.construct.hash.W 16 (BitVec.ofNat 64 used) = p.construct.hash.W := by
      funext i
      by_cases hi : i = 16 <;> simp [upd, hi, hused]
    refine ⟨used, 3, Vu, hu, Lt, ?_, ?_, ?_, ?_, ?_, ?_, kt.2.1.trans rdu, kt.2.2.trans wru⟩
    · rw [hself]; exact Rt
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff p.pPrime (Nat.le_of_lt hlen.2), up]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff p.exponentPrime (Nat.le_of_lt hlen.2), ue]
    · simp [PPrimalityPlan.result, hsmall]
    · intro b rest hr
      simp only [PPrimalityPlan.result, hsmall, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨rfl, by simp only [List.length_drop]; omega⟩
    · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
        (ff.mono (fun r hr => List.mem_append_right _ hr))
  · have domain : VG.Proof.Dsa.Generation.PDomain p.construct.len p.construct.value :=
      ⟨p.construct.width, ho, Nat.le_of_not_gt hsmall, hb⟩
    let call := p.call domain
    have tape := source_of_frame htape fu p.tapeConstruct p.randMax rdu wru
    let bs := Spec.Rsa.bytesAt u.mem (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len
    have blen : bs.length = p.construct.len := bytesAt_length _ _ _
    have bval : Spec.Rsa.os2ip bs = p.construct.value := by
      dsimp only [bs]
      rw [up, ← VG.Proof.Dsa.decodeBE_os2ip]
      exact VG.Proof.Dsa.decodeBE_encodeBE hbound
    have src : Src u p.construct.B p.construct.Z
        (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) bs := by
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        obtain ⟨r, hr, hc⟩ := hs.pWrite i (blen ▸ hi)
        rw [rdu, wru]
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      · intro i hi; simp [bs, Spec.Rsa.bytesAt]
      · intro i hi; exact p.construct.pOutside i (blen ▸ hi)
    refine WP.mono (pTest_full_ok M K (p := call) Lu Ru wu hp hbound up hread hsmall
      rfl rfl rfl rfl hused hu tape (fun i hi => by rw [wru]; exact hwitness i hi) blen bval src)
      fun t ⟨used', status, hbound', Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
    dsimp only [call, PPrimalityPlan.call, PPrimalityPlan.prime] at he hr
    refine ⟨used', status, Vu, hbound', Lt, Rt, ?_, ?_, ?_, ?_, ?_, rdt.trans rdu, wrt.trans wru⟩
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft p.pPrime (Nat.le_of_lt hlen.2), up]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft p.exponentPrime (Nat.le_of_lt hlen.2), ue]
    · simpa only [PPrimalityPlan.result, hsmall, ite_false] using he
    · simpa only [PPrimalityPlan.result, hsmall, ite_false] using hr
    · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
        (ft.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation
