module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateWidth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash

/-! ### `Dsa.X86_64.Generation.PBuild`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.HashStep`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86_64.Generation.HashSequence`, which this module and modules that import it used -/

section

/-! # All p-candidate hash contributions, with bounded public sequencing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashPrefix_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) (k : Nat) (hk : k ≤ p.count + 1)
    {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashPrefix G p.len p.count k) s fun t =>
      HashState p Hs k t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem := by
  induction k generalizing s with
  | zero =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    have he : WP isa (.block []) s (fun t => t = s) := by xrun
    exact WP.mono he fun t h => by
      subst t
      exact ⟨hs, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ k ih =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    refine WP.seq (WP.mono (ih (by omega_using [hk]) hs) fun u ⟨hu, rdu, wru, csu, hfu⟩ => ?_)
    refine WP.mono (hashStep_ok hG hHh hsize hd (by omega_using [hk]) hu) fun t ⟨ht, rdt, wrt, cst, hft⟩ => ?_
    exact ⟨ht, rdt.trans rdu, wrt.trans wru, fun r hr => (cst r hr).trans (csu r hr), hfu.trans hft⟩

theorem pHashes_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count) s fun t =>
      HashState p Hs (p.count + 1) t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem :=
  hashPrefix_ok hG hHh hsize hd _ (Nat.le_refl _) hs

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PShape`, which only this module used -/

section

/-! # The native hash-suffix shaper feeds exactly the specified reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem pShape_ok {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) (q : Nat) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      (∀ a, (∀ i < plen, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rdi, .rsi, .rcx, .rdx, .rax, .r8, .r9, .r10, .r11] s t := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.X86_64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot p.size.2.2 hlmax)
    fun u ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.2.1, hk.2.2]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega_using [hl] : 9 ≤ 8 * plen) (by omega_using [hlmax]) (by rw [hbl]; omega_using [])
    hsi hdi (by rw [hbl]; exact hcx) hdx hrd
    (fun i hi => by rw [hk.2.2]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨_, hx, hf, kt⟩ => ?_
  dsimp only
  rw [hbl] at hx
  refine ⟨?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) + 1 -
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % (2 * q) = _
    rw [hx]
    exact hash_shaped_candidate hs (by omega_using [hl]) rfl hroom hcount hhash hsize q
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % 2 = 1 ∧
      2 ^ (8 * plen - 1) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) < 2 ^ (8 * plen)
    rw [hx]
    exact VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * plen) (by omega_using [hl]) _
  · intro a ha
    rw [hf a (fun i hi => ha i (hbl ▸ hi)), hm]

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Hash and shape the complete unreduced p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pBuild_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p H 0 s)
    {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j)
    (hbuf : HashBufferSeparate p.F p.S op plen) (q : Nat) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      Lay t p.F p.S ∧ (∃ V, Rep t.mem p.F p.S V p.W) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
  refine WP.seq (WP.mono (pHashes_ok hG hHh hsize hd hs)
    fun u ⟨hu, rdu, wru, csu, hfu⟩ => ?_)
  refine WP.mono (pShape_ok hu hl hlmax hroom hcount hhash hseedsize hop
    (fun i hi => wru ▸ hout i hi) hsep q) fun t ⟨hx, hb, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hu.rep
  have Rt := rep_of_external_write R hbuf hf
  refine ⟨hx, hb, lay_of_rep hu.layout R Rt rfl (hk.gpr (by decide)) hk.2.2,
    ⟨V, Rt⟩, hk.2.1.trans rdu, hk.2.2.trans wru, ?_, ?_⟩
  · intro r hr
    have hr' : r ∉ [.rdi, .rsi, .rcx, .rdx, .rax, .r8, .r9, .r10, .r11] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hk.gpr hr').trans (csu r hr)
  · intro a ha
    rw [hf a (fun i hi he => ha ⟨op, plen⟩ (by simp) (he ▸
      Offset.contains_base op (by omega_using [hi]) (by omega_using [hlmax, hi])))]
    exact hfu a (fun r hr => ha r (List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.CandidateWidth`, which this module and modules that import it used -/

section

/-! # The native p-width branch matches the specification's guard -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64

theorem candidateWidth_ok {s : State} {B pp : Addr} {Z w len p : Nat}
    (h : Ws s B Z w) (hptr : word s.mem B 160 = pp)
    (hlen : 0 < len) (hbound : p < 256 ^ len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp len = Spec.Dsa.encodeBE len p)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) :
    WP isa (.block Impl.Dsa.X86_64.Generation.candidateWidth) s fun t =>
      t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t := by
  have hfirst : s.mem pp = (Spec.Dsa.encodeBE len p).getD 0 0 := by
    rw [← hbytes]
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hlen]
  have he := VG.Proof.Dsa.Generation.candidate_firstByte hlen hbound
  rw [← hfirst] at he
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t =>
      t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.candidateWidth, State.ea, hdr, hdrOff, at0, h.rdi,
      show BitVec.ofInt 64 0 = 0#64 by rfl, BitVec.add_zero,
      h.scr.ld (d := 160) (by have := h.h256; omega_using [this]), hptr, hrd]
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (s.mem pp).isLt (by decide : 2 ^ 8 < 2 ^ 64))]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact he) rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PConstruct`, which this module and modules that import it used -/

section

/-! # Complete verified construction of p and its generator exponent -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/CandidateFromFrame.lean`, which only this module imported.
section

/-! # Candidate arithmetic and output storage from retained frame arguments -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Dsa.Generation.Layout

theorem candidateFromFrame_ok {s : State} {B F : Addr} {Z w pLen qLen : Nat}
    {W : Nat → BitVec 64} {xb qb : List Byte}
    (h : Ws s B Z w) (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen)
    (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (sx : Src s B Z (off (W 5) shaped) xb) (sq : Src s B Z (off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < pLen, InRegions s.wr (off (off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (off (off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, off (off (W 5) p) i ≠ off (off (W 5) exponent) j) :
    WP isa (candidateFromFrame pLen qLen) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = off (W 5) p ∧ Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hpl : pLen < 2 ^ 31 := by have := h.w2; omega
  have hql : qLen < 2 ^ 31 := by omega
  unfold candidateFromFrame
  refine WP.seq (WP.mono (candidateArguments_ok h hpl hql hsp hr hwords hsep)
    fun u ⟨hu, hxp, hxl, hqp, hqlen, hpp, hep, hm, hf, hk⟩ => ?_)
  have frame : Frm B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_singleton, forall_eq]
    exact h.h256
  have sxu := sx.congrK (InScr.of_frm frame bound) hk
  have squ := sq.congrK (InScr.of_frm frame bound) hk
  refine WP.mono (candidateBuild_ok hu hxp (by rw [hx]; exact hxl) hqp (by rw [hq]; exact hqlen)
    hpp hep hm sxu squ (hx.trans hpLen) (by omega) (by omega) hqpos hqfit
    (fun i hi => by rw [hk.2.2]; exact hpw i (hpLen ▸ hi))
    (fun i hi => by rw [hk.2.2]; exact hew i (hpLen ▸ hi))
    (fun i hi => hpo i (hpLen ▸ hi)) (fun i hi => heo i (hpLen ▸ hi))
    (fun i hi j hj => hpe i (hpLen ▸ hi) j (hpLen ▸ hj))) fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  rw [← hpLen] at tp te ft
  refine ⟨tp, te, ht, hp, ?_, (hk.trans kt).mono (by decide)⟩
  have ff : Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem u.mem := by
    intro a ha
    apply hf a
    right
    have hn := ha ⟨B, Z⟩ (by simp)
    change ¬ ofs B a < Z at hn
    have := h.h256
    omega
  exact ff.trans ft

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ReduceFromFrame.lean`, which only this module imported.
section

/-! # Reduce the shaped candidate from an uninitialized arithmetic workspace -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Generation.Layout

theorem reduceFromFrame_ok {s : State} {B F S : Addr} {Z w pLen qLen : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {xb qb : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hS : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hZ : slot w 16 ≤ Z) (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24)
    (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (hframe : ∀ k < 37, ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i))
    (sx : Src s B Z (off (W 5) shaped) xb) (sq : Src s B Z (off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < pLen, InRegions s.wr (off (off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (off (off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, off (off (W 5) p) i ≠ off (off (W 5) exponent) j) :
    WP isa (seqs [.block Impl.Dsa.X86_64.Generation.workspaceBase,
      Impl.Dsa.X86_64.Generation.workspace w, Impl.Dsa.X86_64.Generation.candidateFromFrame pLen qLen]) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = off (W 5) p ∧
      Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  have squ := sq.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hS.congr ku.2.2) hdi hZ hw1 hw2)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  have hb : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  refine WP.mono (candidateFromFrame_ok hv hpLen hqLen
    ((kv.gpr (by decide)).trans ((ku.gpr (by decide)).trans L.rsp))
    (fun k hk => by rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact L.ld (by unfold VG.Impl.RsaOaep.X86_64.frameBytes; omega))
    (fun k hk => by rw [frame_word_of_workspace fv hb (hframe k hk), hm]; exact R.fr k hk)
    hsep (sxu.congrK (InScr.of_frm fv hb) kv) (squ.congrK (InScr.of_frm fv hb) kv)
    hx hq hqposlen hqpos hqfit
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hpw i hi)
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hew i hi) hpo heo hpe)
    fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  refine ⟨tp, te, ht, hp, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  have fs : Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem v.mem := by
    intro a ha
    rw [fv a (fun r hr => Or.inr (Nat.le_trans (hb r hr) (by
      have hn := ha ⟨B, Z⟩ (by simp)
      change ¬ ofs B a < Z at hn
      omega))), hm]
  exact fs.trans ft

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pConstruct_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : PConstructPlan} (hd : G.D = p.hash.len) {s : State} (hs : PConstructState p H s)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.hash.len) bs).length = 8 * p.hash.len) :
    WP isa (Impl.Dsa.X86_64.Generation.pConstruct G p.len p.hash.len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (p.hash.W 5) Impl.Dsa.Generation.Layout.p) p.len =
        Spec.Dsa.encodeBE p.len p.value ∧
      Spec.Rsa.bytesAt t.mem (off (p.hash.W 5) exponent) p.len =
        Spec.Dsa.encodeBE p.len ((p.value - 1) / Spec.Rsa.os2ip p.qb) ∧
      p.value % 2 = 1 ∧ p.value < 2 ^ (8 * p.len) ∧
      Lay t p.hash.F p.hash.S ∧ (∃ V, Rep t.mem p.hash.F p.hash.S V p.hash.W) ∧
      Ws t p.B p.Z (p.len / 8) ∧
      word t.mem p.B 160 = off (p.hash.W 5) Impl.Dsa.Generation.Layout.p ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hl : 2 ≤ p.len ∧ p.len ≤ 1024 ∧ p.len = 8 * (p.len / 8) ∧
      2 ≤ p.len / 8 ∧ p.len / 8 < 2 ^ 24 := by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
  have hql : p.hash.len ≤ p.len := by rcases p.hash.width with hh | hh <;> rcases p.width with hp | hp | hp <;> omega_using [hh, hp]
  unfold Impl.Dsa.X86_64.Generation.pConstruct
  rw [← p.hashCount]
  refine WP.seq (WP.mono (pBuild_ok hG hHh hsize hd hs.hash hl.1 hl.2.1 p.hashRoom
    p.hashCount hhash hseedsize p.shapedSlot hs.shapedWrite p.shapedInput p.shapedHash
    (Spec.Rsa.os2ip p.qb)) fun u ⟨he, hx, Lu, ⟨Vu, Ru⟩, rdu, wru, _, fu⟩ => ?_)
  let xb := Spec.Rsa.bytesAt u.mem (off (p.hash.W 5) shaped) p.len
  have hxb : xb.length = p.len := bytesAt_length _ _ _
  have sx : Src u p.B p.Z (off (p.hash.W 5) shaped) xb := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [hxb] at hi
      obtain ⟨r, hr, hc⟩ := hs.shapedWrite i hi
      rw [rdu, wru]
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · intro i hi; simp [xb, Spec.Rsa.bytesAt]
    · intro i hi; exact p.shapedOutside i (hxb ▸ hi)
  have sq := source_of_frame hs.qSource fu p.qHash (by rw [p.qLength]; have := p.hash.size; omega_using [this]) rdu wru
  refine WP.mono (reduceFromFrame_ok Lu Ru (hs.scratch.congr wru) p.base p.workspaceRoom
    hl.2.2.2.1 hl.2.2.2.2 hl.2.2.1 hql p.frameHeaders p.frameOutside sx sq hxb p.qLength
    (by rcases p.hash.width with hh | hh <;> omega_using [hh]) p.qPositive p.qFits
    (fun i hi => by rw [wru]; exact hs.pWrite i hi)
    (fun i hi => by rw [wru]; exact hs.exponentWrite i hi)
    p.pOutside p.exponentOutside p.pExponent) fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  have hvalue : Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip p.qb) = p.value := he
  have Rt := rep_of_disjoint_frame Ru ft p.frameArithmetic p.hashArithmetic
  refine ⟨by rw [tp, hvalue], by rw [te, hvalue], ?_, ?_,
    lay_of_rep Lu Ru Rt rfl (kt.gpr (by decide)) kt.2.2, ⟨Vu, Rt⟩, ht, hp, ?_,
    kt.2.1.trans rdu, kt.2.2.trans wru⟩
  · rw [← hvalue]; exact VG.Proof.Dsa.Generation.pReduction_odd _ _
  · rw [← hvalue]
    exact Nat.lt_of_le_of_lt (VG.Proof.Dsa.Generation.pReduction_le hx.1).2 hx.2.2
  · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
      (ft.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # A p candidate is constructed and tested entirely by verified native code -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PTestFull.lean`, which only this module imported.
section

/-! # A full-width p candidate is tested by the probable-prime function -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64

theorem PrimeCallPlan.bits_eq (p : PrimeCallPlan) : 8 * p.prime.len = p.bits := by
  rw [p.len]; rcases p.supported with h | h | h | h | h <;> rw [h]

theorem pTest_full_ok (T : PrimeTest) {p : PrimeCallPlan} {used : Nat} {s : State}
    {V : Nat → Byte} {pp : Addr}
    (L : Lay s p.prime.sp p.hash) (R : Rep s.mem p.prime.sp p.hash V p.W)
    (h : Ws s p.prime.B p.prime.Z p.prime.w)
    (hptr : word s.mem p.prime.B 160 = pp)
    (hbound : p.prime.N < 256 ^ p.prime.len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hfull : ¬ p.prime.N < 2 ^ (8 * p.prime.len - 1))
    (hcandidate : Impl.Dsa.X86_64.ProbablePrime.candidate p.bits = Impl.Dsa.Generation.Layout.p)
    (hused : p.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.prime.rand.length)
    (hA : Scr s (p.W 5) Impl.Dsa.Generation.Layout.domainCheck)
    (htc : Covers [⟨p.prime.rp, p.prime.rand.length⟩] (s.rd ++ s.wr))
    (htape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand)
    (hcand : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off (p.W 5) Impl.Dsa.Generation.Layout.p)
      p.prime.len) = p.prime.N) :
    WP isa (Impl.Dsa.X86_64.Generation.pTest T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status, used' ≤ p.prime.rand.length ∧ Lay t p.prime.sp p.hash ∧
        Rep t.mem p.prime.sp p.hash V (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr (by have := p.prime.len2; omega)
    hbound hbytes hrd) fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem p.prime.sp p.hash V p.W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl (ku.gpr (by decide)) ku.2.2
  refine WP.ite false (by simp [eval, hcf, hfull]) (fun he => Bool.noConfusion he) (fun _ => ?_)
  rw [p.bits_eq]
  have hin : PrimeCallInputs p.bits p.prime.sp p.hash (p.W 5) p.prime.rp p.prime.rand p.prime.N used p.W V u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := hA.congr ku.2.2
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := hused
    usedBound := hu
    tapeSize := p.prime.randMax
    tapeCover := by rw [ku.2.1, ku.2.2]; exact htc
    tapeBytes := by rw [hm]; exact bytes_of_src htape
    candidate := by rw [hcandidate, hm, ← p.bits_eq, Nat.mul_div_cancel_left _ (by decide)]; exact hcand
    odd := p.prime.odd
    bitLen := by rw [p.prime.bitLength_eq, p.bits_eq] }
  refine WP.mono (primeCall_ok T p.supported hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  refine ⟨used', status, hb, Lt, Rt, he, hr, ?_, rdt.trans ku.2.1, wrt.trans ku.2.2⟩
  rw [p.changed_eq, ← hm]
  exact ft

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PTestSmall.lean`, which only this module imported.
section

/-! # Undersized p candidates retry without consuming witness bytes -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64

theorem pTest_small_ok {s : State} {B F S pp : Addr} {Z w len value : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64}
    (prime : Prog isa)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (h : Ws s B Z w) (hptr : word s.mem B 160 = pp)
    (hlen : 0 < len) (hbound : value < 256 ^ len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp len = Spec.Dsa.encodeBE len value)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hsmall : value < 2 ^ (8 * len - 1)) :
    WP isa (Impl.Dsa.X86_64.Generation.pTest prime len) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 3)) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.rsi, .rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr hlen hbound hbytes hrd)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl (ku.gpr (by decide)) ku.2.2
  refine WP.ite true (by simp [eval, hcf, hsmall]) (fun _ => ?_) (fun he => Bool.noConfusion he)
  refine WP.mono (stackStatus_ok Lu Ru 3 (by decide)) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  exact ⟨Lt, Rt, hm ▸ ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

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
    (hsize : ∀ bytes, (H.hash bytes).length = G.D) (T : PrimeTest)
    {p : PPrimalityPlan} (hd : G.D = p.construct.hash.len) {s : State}
    (hs : PConstructState p.construct H s)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.construct.hash.len) bs).length = 8 * p.construct.hash.len)
    {used : Nat} (hused : p.construct.hash.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.length)
    (htape : Src s p.construct.B p.construct.Z p.rp p.rand)
    (hA : Scr s (p.construct.hash.W 5) domainCheck)
    (htc : Covers [⟨p.rp, p.rand.length⟩] (s.rd ++ s.wr)) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.pConstruct G p.construct.len p.construct.hash.len)
      (Impl.Dsa.X86_64.Generation.pTest T.run p.construct.len)) s (PConstructTestEnd p used s) := by
  refine WP.seq (WP.mono (pConstruct_ok hG hHh hsize hd hs hhash hseedsize)
    fun u ⟨up, ue, ho, hb, Lu, ⟨Vu, Ru⟩, wu, hp, fu, rdu, wru⟩ => ?_)
  have hlen : 0 < p.construct.len ∧ p.construct.len < 2 ^ 64 := by
    rcases p.construct.width with hh | hh | hh <;> omega_using [hh]
  have hbound : p.construct.value < 256 ^ p.construct.len := by
    simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb
  have hread : InRegions (u.rd ++ u.wr) (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) 1 := by
    obtain ⟨r, hr, hc⟩ := hs.pWrite 0 hlen.1
    rw [rdu, wru]
    exact ⟨r, List.mem_append_right _ hr, by simpa [off] using hc⟩
  by_cases hsmall : p.construct.value < 2 ^ (8 * p.construct.len - 1)
  · refine WP.mono (pTest_small_ok T.run Lu Ru wu hp hlen.1 hbound up hread hsmall)
      fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    have ff : Frame p.testWrites u.mem t.mem := by
      intro a ha
      apply ft a
      right
      have hn := ha ⟨p.construct.hash.F, frameBytes⟩ (by simp [PPrimalityPlan.testWrites])
      change ¬ ofs p.construct.hash.F a < frameBytes at hn
      unfold frameBytes at hn
      omega_using [hn]
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
      exact ⟨rfl, by simp only [List.length_drop]; omega_using [hu]⟩
    · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
        (ff.mono (fun r hr => List.mem_append_right _ hr))
  · have domain : VG.Proof.Dsa.Generation.PDomain p.construct.len p.construct.value :=
      ⟨p.construct.width, ho, Nat.le_of_not_gt hsmall, hb⟩
    let call := p.call domain
    have tape := source_of_frame htape fu p.tapeConstruct p.randMax rdu wru
    have hcand : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem
        (off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len) = p.construct.value := by
      rw [up]; exact VG.Proof.Dsa.decodeBE_encodeBE hbound
    have hcandidate : Impl.Dsa.X86_64.ProbablePrime.candidate call.bits = Impl.Dsa.Generation.Layout.p := by
      change (if 8 * p.construct.len ≤ 256 then _ else _) = _
      exact ite_eq_right (by rcases p.construct.width with hh | hh | hh <;> omega_using [hh])
    refine WP.mono (pTest_full_ok T (p := call) Lu Ru wu hp hbound up hread hsmall hcandidate hused hu
      (hA.congr wru) (by rw [rdu, wru]; exact htc) tape hcand)
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
