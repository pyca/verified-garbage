module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Bignum.Octets
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.TCB.AArch64.Isa

/-! ### `Dsa.AArch64.Generation.HashStep`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.PSeedHash`, which this module and modules that import it used -/

section

/-! Each contribution hashes the original seed plus its wrapped public offset. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pSeedHash_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op : Addr} {len offset j : Nat}
    (hlen : len < 4096) (hj : j < 4096) (hc : offset + j < 2 ^ 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) :
    WP isa (Impl.Dsa.AArch64.Generation.pSeedHash G len j) s fun t =>
      Lay t F S ∧ Step F S [⟨op, len⟩] s t ∧
      Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem (off S oDig) G.D =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.AArch64.Generation.pSeedHash
  refine WP.seq (WP.mono (seedInputArgs_ok hj L R hrp hop hoff) fun u ⟨hu1, hu2, hu0, hm, ku⟩ => ?_)
  let bs := Spec.Rsa.bytesAt s.mem rp len
  have hbl : bs.length = len := VG.Proof.Bignum.bytesAt_length _ _ _
  have hread : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [ku.rd, ku.wr]
    exact hrd i (hbl ▸ hi)
  have hwrite : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
    intro i hi
    rw [ku.wr]
    exact hwr i (hbl ▸ hi)
  have hbytes : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hbl] at hi
    rw [hm]
    simp [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hseed := seedAdd_ok bs (hbl ▸ hlen) hc hu1 hu2 hu0 hread hwrite hbytes
    (fun i hi k hk => hsep i (hbl ▸ hi) k (hbl ▸ hk))
  rw [hbl] at hseed
  refine WP.seq (WP.mono hseed fun v ⟨hv, hf, kv⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Rv := rep_of_external_write Ru hbuf hf
  have Lu := L.congr ku.sp ku.wr (by rw [hm])
  have Lv := lay_of_rep Lu Ru Rv rfl kv.sp kv.wr
  have Av := A.congr (kv.rd.trans ku.rd) (kv.wr.trans ku.wr) rfl rfl
  refine WP.mono (hash_bytes_frame hG hHh hsize Lv Rv Av)
    fun t ⟨Lt, step, hft, V', Rt, _, hb⟩ => ?_
  have hfs : Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem v.mem := by
    intro a ha
    rw [hf a (fun i hi => fun he => ha ⟨op, len⟩ (by simp) (he ▸
      Offset.contains_base op (by omega_using [hi]) (by omega_using [hlen, hi]))), hm]
  have hfinal := hfs.trans (hft.mono (by simp))
  have k := ku.trans kv
  refine ⟨Lt, ⟨step.rd.trans k.rd, step.wr.trans k.wr, step.sp.trans k.sp, ?_,
    (fun r hr => (step.vec r hr).trans (k.vcs r hr)), hfinal.mono (by simp)⟩, hfinal, ⟨V', Rt⟩, ?_⟩
  · intro r hr h30
    rw [step.cs r hr h30]
    exact k.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | decide | exact (h30 rfl).elim)
  · rw [hb, hv]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PHashOne`, which only this module used -/

section

/-! # Construct and store one p-candidate hash contribution in assembly -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pHashOne_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
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
    WP isa (Impl.Dsa.AArch64.Generation.pHashOne G len count j) s fun t =>
      Lay t F S ∧ Step F S [⟨dp, len⟩, ⟨op, len⟩] s t ∧
      Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem dp len =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.AArch64.Generation.pHashOne
  refine WP.seq (WP.mono (pSeedHash_ok hG hHh hsize (by omega_using [hlen]) (by omega_using [hcount, hj]) hc L R A hrp hop hoff hrd hwr hsep hbuf)
    fun u ⟨Lu, step, hfu, ⟨V', Ru⟩, hb⟩ => ?_)
  refine WP.seq (WP.mono (hashCopyArgs_ok hlen hcount Lu Ru hhp) fun v ⟨hsi, hdi, hcx, hm, kv⟩ => ?_)
  rw [hdp] at hdi
  let digest := Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j)))
  have hdl : digest.length = len := (hsize _).trans hd
  have hread : ∀ i < digest.length, InRegions (v.rd ++ v.wr) (off (off S oDig) i) 1 := by
    intro i hi
    rw [hdl] at hi
    rw [kv.rd, kv.wr, off_off]
    exact Lu.sld (o := oDig + i) (n := 1) (by dsimp only [oDig, oRsa]; omega_using [hlen, hi])
  have hbytes : ∀ i < digest.length, v.mem (off (off S oDig) i) = digest.getD i 0 := by
    intro i hi
    rw [hdl] at hi
    rw [hm]
    change _ = (Hs.hash _).getD i 0
    rw [← hb, hd]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hcopy := random_copyRest_ok hsi hdi (by rw [hdl]; exact hcx)
    (by rw [hdl]; rcases hlen with rfl | rfl <;> omega_using []) hread
    (fun i hi => by rw [kv.wr, step.wr]; exact hwd i (hdl ▸ hi))
    (by
      intro i hi k hk
      rw [hdl] at hi hk
      change off (off S oDig) i ≠ off dp k
      rw [off_off]
      exact Ne.symm (hdbuf.scratch k hk (oDig + i) (by dsimp only [oDig, oRsa]; omega_using [hlen, hi])))
  rw [hdl] at hcopy
  refine WP.mono hcopy fun t ⟨hout, hf, kt⟩ => ?_
  have Rv : Rep v.mem F S V' W := hm ▸ Ru
  have Rt := rep_of_external_write Rv hdbuf hf
  have Lv := Lu.congr kv.sp kv.wr (by rw [hm])
  have hft : Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] u.mem t.mem := by
    intro a ha
    rw [hf a (fun i hi => fun he => ha ⟨dp, len⟩ (by simp) (he ▸
      Offset.contains_base dp (by omega_using [hi]) (by omega_using [hlen, hi]))), hm]
  have hfinal := (hfu.mono (by simp)).trans hft
  have k := kv.trans kt
  refine ⟨lay_of_rep Lv Rv Rt rfl kt.sp kt.wr,
    ⟨k.rd.trans step.rd, k.wr.trans step.wr, k.sp.trans step.sp, ?_,
      (fun r hr => (k.vcs r hr).trans (step.vec r hr)), hfinal.mono (by simp)⟩,
    hfinal, ⟨V', Rt⟩, ?_⟩
  · intro r hr h30
    rw [k.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | decide | exact (h30 rfl).elim)]
    exact step.cs r hr h30
  · apply List.ext_getElem
    · rw [VG.Proof.Bignum.bytesAt_length, hdl]
    · intro i hi hi'
      have hil : i < len := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (dp + BitVec.ofNat 64 i) = digest[i]'(by rw [hdl]; exact hil)
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < digest.length from hdl ▸ hil), Option.getD_some] using
        (hout i hil).trans (hbytes i (hdl ▸ hil))

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Advance the native hash-contribution sequence -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.Dsa.Generation

theorem hashStep_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} {k : Nat} (hk : k ≤ p.count)
    (hs : HashState p Hs k s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashOne G p.len p.count k) s fun t =>
      HashState p Hs (k + 1) t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem := by
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
    p.wrapped_sep (p.dest_sep k)) fun t ⟨Lt, step, hf, Rt, hout⟩ => ?_
  have hframe : Frame p.changed s.mem t.mem := hf.sub (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨p.output, (p.count + 1) * p.len⟩, by simp [HashPlan.changed], p.dest_sub k⟩
    all_goals exact ⟨_, by simp [HashPlan.changed], fun _ h => h⟩)
  have rd := step.rd
  have wr := step.wr
  refine ⟨⟨Lt, Rt, hs.hashArgs.congr rd wr rfl rfl,
    (fun i hi => by rw [rd, wr]; exact hs.seedRead i hi),
    (fun i hi => by rw [wr]; exact hs.wrappedWrite i hi),
    (fun i hi => by rw [wr]; exact hs.outputWrite i hi), ?_, ?_⟩, ⟨rd, wr, step.sp, step.cs, step.vec, hframe.mono (by simp [HashPlan.changed])⟩, hframe⟩
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

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.HashSequence`, which this module and modules that import it used -/

section

/-! # All p-candidate hash contributions, with bounded public sequencing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hashPrefix_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) (k : Nat) (hk : k ≤ p.count + 1)
    {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashPrefix G p.len p.count k) s fun t =>
      HashState p Hs k t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem := by
  induction k generalizing s with
  | zero =>
    unfold Impl.Dsa.AArch64.Generation.pHashPrefix
    have he : WP isa (.block []) s (fun t => t = s) := by brun
    exact WP.mono he fun t h => by
      subst t
      exact ⟨hs, Step.refl _ _ _ _, Frame.refl _ _⟩
  | succ k ih =>
    unfold Impl.Dsa.AArch64.Generation.pHashPrefix
    refine WP.seq (WP.mono (ih (by omega_using [hk]) hs) fun u ⟨hu, su, hfu⟩ => ?_)
    refine WP.mono (hashStep_ok hG hHh hsize hd (by omega_using [hk]) hu) fun t ⟨ht, st, hft⟩ => ?_
    exact ⟨ht, su.trans st, hfu.trans hft⟩

theorem pHashes_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashes G p.len p.count) s fun t =>
      HashState p Hs (p.count + 1) t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem :=
  hashPrefix_ok hG hHh hsize hd _ (Nat.le_refl _) hs

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PShape`, which only this module used -/

section

/-! # The native hash-suffix shaper feeds exactly the specified reduction -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem pShape_ok {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) (q : Nat) :
    WP isa (Impl.Dsa.AArch64.Generation.pShape p.len p.count plen) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      (∀ a, (∀ i < plen, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.x0, .x2, .x4, .x9, .x12, .x13, .x14] s t := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.AArch64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot (by have hc := p.count_le; rcases p.width with h | h <;> rw [h] <;> omega_using [hc]) hlmax)
    fun u ⟨hdi, hsi, hcx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.rd, hk.wr]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (qShape_ok (by rw [hbl]; exact hl) (by rw [hbl]; omega_using [hlmax])
    hsi hdi (by rw [hbl]; exact hcx) hrd
    (fun i hi => by rw [hk.wr]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨houtbytes, hf, kt⟩ => ?_
  have hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) =
      Spec.Ffdh.candidateOf (8 * plen) (Spec.Rsa.os2ip bs) := by
    rw [← hbl, houtbytes]
    exact VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
      (by intro he; have := congrArg List.length he; simp only [List.length_nil, hbl] at this; omega_using [hl, this])
      (by decide : 7 < 8) (by rw [hbl]; omega_using [hl])
  dsimp only
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

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Hash and shape the complete unreduced p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pBuild_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
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
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.AArch64.Generation.pShape p.len p.count plen)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      Lay t p.F p.S ∧ (∃ V, Rep t.mem p.F p.S V p.W) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      Step p.F p.S [⟨op, plen⟩, ⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
  refine WP.seq (WP.mono (pHashes_ok hG hHh hsize hd hs)
    fun u ⟨hu, su, hfu⟩ => ?_)
  refine WP.mono (pShape_ok hu hl hlmax hroom hcount hhash hseedsize hop
    (fun i hi => su.wr ▸ hout i hi) hsep q) fun t ⟨hx, hb, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hu.rep
  have Rt := rep_of_external_write R hbuf hf
  have hframe : Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
    intro a ha
    rw [hf a (fun i hi he => ha ⟨op, plen⟩ (by simp) (he ▸
      Offset.contains_base op (by omega_using [hi]) (by omega_using [hlmax, hi])))]
    exact hfu a (fun r hr => ha r (List.mem_cons_of_mem _ hr))
  refine ⟨hx, hb, lay_of_rep hu.layout R Rt rfl hk.sp hk.wr,
    ⟨V, Rt⟩, hk.rd.trans su.rd, hk.wr.trans su.wr,
    ⟨hk.rd.trans su.rd, hk.wr.trans su.wr, hk.sp.trans su.sp, ?_,
      (fun r hr => (hk.vcs r hr).trans (su.vec r hr)),
      hframe.mono (by simp [HashPlan.changed])⟩, hframe⟩
  intro r hr h30
  rw [hk.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | decide | exact (h30 rfl).elim)]
  exact su.cs r hr h30

end VG.Proof.Dsa.AArch64.Generation
