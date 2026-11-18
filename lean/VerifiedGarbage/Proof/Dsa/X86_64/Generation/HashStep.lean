module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.Generation.PSeedHash`, which this module and modules that import it used -/

section

/-! # Hash one wrapped seed while preserving the frame and external tapes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pSeedHash_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op : Addr} {len offset j : Nat}
    (hlen : len < 2 ^ 31) (hj : j < 2 ^ 31) (hc : offset + j < 2 ^ 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) :
    WP isa (Impl.Dsa.X86_64.Generation.pSeedHash G len j) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem (off S oDig) G.D =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.X86_64.Generation.pSeedHash
  refine WP.seq (WP.mono (seedInputArgs_ok hj L R hrp hop hoff) fun u ⟨hsi, hdi, hax, hm, ku⟩ => ?_)
  let bs := Spec.Rsa.bytesAt s.mem rp len
  have hbl : bs.length = len := bytesAt_length _ _ _
  have hread : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [ku.2.1, ku.2.2]
    exact hrd i (hbl ▸ hi)
  have hwrite : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
    intro i hi
    rw [ku.2.2]
    exact hwr i (hbl ▸ hi)
  have hbytes : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hbl] at hi
    rw [hm]
    simp [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hseed := seedAdd_ok bs (hbl ▸ hlen) hc hsi hdi hax hread hwrite hbytes
    (fun i hi k hk => hsep i (hbl ▸ hi) k (hbl ▸ hk))
  rw [hbl] at hseed
  refine WP.seq (WP.mono hseed fun v ⟨hv, hf, kv⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Rv := rep_of_external_write Ru hbuf hf
  have Lu := L.congr (ku.gpr (by decide)) ku.2.2 (by rw [hm])
  have Lv := lay_of_rep Lu Ru Rv rfl (kv.gpr (by decide)) kv.2.2
  have Av := A.congr (kv.2.1.trans ku.2.1) (kv.2.2.trans ku.2.2) rfl rfl
  refine WP.mono (hash_bytes_frame hG hHh hsize Lv Rv Av)
    fun t ⟨Lt, rd, wr, cs, hft, V', Rt, _, hb⟩ => ?_
  refine ⟨Lt, rd.trans (kv.2.1.trans ku.2.1), wr.trans (kv.2.2.trans ku.2.2), ?_, ?_, ⟨V', Rt⟩, ?_⟩
  · intro r hr
    rw [cs r hr, keep_cs' kv (cs_disj _ (by decide)) r hr,
      keep_cs' ku (cs_disj _ (by decide)) r hr]
  · have hfs : Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem v.mem := by
      intro a ha
      rw [hf a (fun i hi => fun he => ha ⟨op, len⟩ (by simp) (he ▸
        Offset.contains_base op (by omega_using [hi]) (by omega_using [hlen, hi]))), hm]
    exact hfs.trans (hft.mono (by simp))
  · rw [hb, hv]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PHashOne`, which only this module used -/

section

/-! # Construct and store one p-candidate hash contribution in assembly -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pHashOne_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op hp dp : Addr} {len offset count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hcount : count ≤ 11) (hj : j ≤ count)
    (hc : offset + j < 2 ^ 32) (hdp : off hp ((count - j) * len) = dp)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hhp : W 4 = hp) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hwd : ∀ i < len, InRegions s.wr (off dp i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) (hdbuf : HashBufferSeparate F S dp len) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashOne G len count j) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem dp len =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.X86_64.Generation.pHashOne
  refine WP.seq (WP.mono (pSeedHash_ok hG hHh hsize (by omega_using [hlen]) (by omega_using [hcount, hj]) hc L R A hrp hop hoff hrd hwr hsep hbuf)
    fun u ⟨Lu, rdu, wru, csu, hfu, ⟨V', Ru⟩, hb⟩ => ?_)
  refine WP.seq (WP.mono (hashCopyArgs_ok hlen hcount Lu Ru hhp) fun v ⟨hsi, hdi, hcx, hdx, hm, kv⟩ => ?_)
  rw [hdp] at hdi
  let digest := Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j)))
  have hdl : digest.length = len := (hsize _).trans hd
  have hread : ∀ i < digest.length, InRegions (v.rd ++ v.wr) (off (off S oDig) i) 1 := by
    intro i hi
    rw [hdl] at hi
    rw [kv.2.1, kv.2.2, off_off]
    exact Lu.sld8 (by dsimp only [oDig, oRsa]; omega_using [hlen, hi])
  have hbytes : ∀ i < digest.length, v.mem (off (off S oDig) i) = digest.getD i 0 := by
    intro i hi
    rw [hdl] at hi
    rw [hm]
    change _ = (Hs.hash _).getD i 0
    rw [← hb, hd]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hcopy := copyDigest_ok (by rw [hdl]; exact hlen) hsi hdi
    (by rw [hdl]; exact hcx) (by rw [hdl]; exact hdx) hread
    (fun i hi => by rw [kv.2.2, wru]; exact hwd i (hdl ▸ hi)) hbytes
    (by
      intro i hi k hk
      rw [hdl] at hi hk
      rw [off_off]
      exact Ne.symm (hdbuf.scratch k hk (oDig + i) (by dsimp only [oDig, oRsa]; omega_using [hlen, hi])))
  rw [hdl] at hcopy
  refine WP.mono hcopy fun t ⟨hout, hf, kt⟩ => ?_
  have Rv : Rep v.mem F S V' W := hm ▸ Ru
  have Rt := rep_of_external_write Rv hdbuf hf
  have Lv := Lu.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  refine ⟨lay_of_rep Lv Rv Rt rfl (kt.gpr (by decide)) kt.2.2,
    kt.2.1.trans (kv.2.1.trans rdu), kt.2.2.trans (kv.2.2.trans wru), ?_, ?_, ⟨V', Rt⟩, hout⟩
  · intro r hr
    rw [keep_cs' kt (cs_disj _ (by decide)) r hr,
      keep_cs' kv (cs_disj _ (by decide)) r hr, csu r hr]
  · have hft : Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] u.mem t.mem := by
      intro a ha
      rw [hf a (fun i hi => fun he => ha ⟨dp, len⟩ (by simp) (he ▸
        Offset.contains_base dp (by omega_using [hi]) (by omega_using [hlen, hi]))), hm]
    exact (hfu.mono (by simp)).trans hft

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Advance the native hash-contribution sequence -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.Dsa.Generation

theorem hashStep_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} {k : Nat} (hk : k ≤ p.count)
    (hs : HashState p Hs k s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashOne G p.len p.count k) s fun t =>
      HashState p Hs (k + 1) t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem := by
  have hls := p.size.2.1
  obtain ⟨V, R⟩ := hs.rep
  have hw : ∀ i < p.len, InRegions s.wr (off (p.dest k) i) 1 := by
    intro i hi
    rw [HashPlan.dest, off_off]
    apply hs.outputWrite
    have hm := Nat.mul_le_mul_right p.len (show p.count - k + 1 ≤ p.count + 1 by omega_using [])
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega_using [hi, hm]
  have hsep : ∀ i < p.len, ∀ j < p.len, off p.seedPtr i ≠ off p.wrapped j := by
    intro i hi j hj he
    have ha : Region.Contains ⟨p.seedPtr, p.len⟩ (off p.seedPtr i) 1 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hls, hi])
    have hb : Region.Contains ⟨p.wrapped, p.len⟩ (off p.wrapped j) 1 := Offset.contains_base _ (by omega_using [hj]) (by omega_using [hls, hj])
    exact p.seed_wrap _ (he ▸ ha) hb
  refine WP.mono (pHashOne_ok hG hHh hsize p.width hd p.count_le hk
    (by omega_using [p.carry, hk]) rfl hs.layout R hs.hashArgs
    p.seed_slot p.wrapped_slot p.output_slot p.offset_slot hs.seedRead hs.wrappedWrite hw hsep
    p.wrapped_sep (p.dest_sep k)) fun t ⟨Lt, rd, wr, cs, hf, Rt, hout⟩ => ?_
  have hframe : Frame p.changed s.mem t.mem := hf.sub (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨p.output, (p.count + 1) * p.len⟩, by simp [HashPlan.changed], p.dest_sub k⟩
    all_goals exact ⟨_, by simp [HashPlan.changed], fun _ h => h⟩)
  refine ⟨⟨Lt, Rt, hs.hashArgs.congr rd wr rfl rfl,
    (fun i hi => by rw [rd, wr]; exact hs.seedRead i hi),
    (fun i hi => by rw [wr]; exact hs.wrappedWrite i hi),
    (fun i hi => by rw [wr]; exact hs.outputWrite i hi), ?_, ?_⟩, rd, wr, cs, hframe⟩
  · rw [frame_bytesAt hframe (by
      intro r hr
      simp only [HashPlan.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact p.seed_output
      · exact p.seed_wrap
      · exact p.seed_scratch
      · exact p.seed_stack) (by omega_using [p.size.2.1])]
    exact hs.seed
  · intro j hj
    by_cases he : j = k
    · subst j
      simpa only [hs.seed, HashPlan.digest, HashPlan.dest] using hout
    · have hjk : j < k := by omega_using [hj, he]
      rw [frame_bytesAt hf (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact p.dest_disjoint (by omega_using [hk, hj]) hk he
        · exact p.output_wrap.sub_left (p.dest_sub j)
        · exact p.output_scratch.sub_left (p.dest_sub j)
        · exact p.output_stack.sub_left (p.dest_sub j)) (by omega_using [p.size.2.1])]
      exact hs.hashes j hjk

end VG.Proof.Dsa.X86_64.Generation
