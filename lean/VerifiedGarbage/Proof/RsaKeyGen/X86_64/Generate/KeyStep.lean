module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Accepted
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key from `p` and `q`

After `q`'s search accepted a prime: the key, which ends the key search with
it or with its failed check, or, for a `d` too small, both primes again in
the same generation.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (candidate_status_guard second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem status_of {s t : State} {status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status)
    (ht : t.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64) :
    t.gpr .rax = BitVec.ofNat 64 status := by
  apply BitVec.eq_of_toNat_eq
  rw [ht, BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (p.kp, 2 * p.L) (by simp [keyOutsOf]), h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  have e (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; rw [Nat.succ_mul]
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L + p.L) = p.slot 8 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L) = p.slot 7 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, e 5,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After `q`: the key. -/
theorem classify_key (hm : Mid p original final used st u) {c : Nat} {pB : List Byte}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .q pB) :
    WP isa (.seq (keyRun keyCall) afterKey) u (Classified p original final used st) := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  obtain ⟨tr, hfin⟩ := hm.final
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hg := drop_lt hpos hrest
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hr0
  refine WP.seq (WP.mono (key_run hm.frame) fun v hk => ?_)
  have hkey : keyOf p u.mem = keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L) := by
    simp only [keyOf, hs4, hs5]
  have hstat := hk.status
  have hout := hk.out
  rw [hkey] at hstat hout
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hwv : word v.mem p.stp 24 = BitVec.ofNat 64 0 := by
    refine Eq.trans (hk.mem.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (Region.sub_prefix (by decide))
  unfold afterKey
  refine WP.seq (WP.mono (candidate_status_guard v) fun w ⟨⟨he1, hax1, hmem1⟩, k1⟩ => ?_)
  have hgw := hk.frame.keep hmem1 k1.2.1 k1.2.2 (fun r hr => k1.gpr (by revert r; decide))
  have hax := status_of hstat hax1
  rw [hstat] at he1
  have hfin' : ∀ {r : KeySearchResult}, keySearch p.L p.eB st ((genRand original).drop used) = r →
      final = r.consume used tr := fun h => by rw [hfin, tailOf, h]
  have hfin0 := hm.final
  cases hkf : keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) with
  | inl res =>
    cases res with
    | ok key =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .ok key) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hout
      refine WP.ite true he1 (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (finish_done (final := final) hgw (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem ?_ ⟨0, by rw [hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr h
      rw [hmem1, key_outs, hout, hks]
      simp only [keySearchBytes, Spec.Entropy.Result.consume, keyBytes, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc]
    | error fl =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .error fl) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hax
      refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
      refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
      have hgw2 := hgw.keep hmem2 k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))
      refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
      refine WP.mono (fail_done (final := final) hgw2 (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem (by rw [hks]; rfl)
        ⟨0, by rw [hmem2, hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr h
  | inr _ =>
    have hks := ks_accepted_small (L := p.L) (eB := p.eB) ho hg hph hkf
    simp only [keyOp, hkf, keyStatus] at he1 hax hout
    refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
    have hgw2 := hgw.keep hmem2 k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (nextPrime_ok hgw2 (phase := 0) (by decide)) fun t ⟨htm, k3⟩ => Or.inl ?_
    have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]
        [(10, (4 : BitVec 64))] := by
      constructor
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
    obtain ⟨h4, hlive⟩ := cont_of (st' := ⟨st.left, .p, limitOf p.L p.eB⟩) hgw2 hv htm k3.2.1 k3.2.2
      (fun r hr => k3.gpr (by revert r; decide)) rfl rfl hgw2.state.left (Nat.le_refl _) hgw2.state.left_lt
      (by rw [hmem2, hmem1]; exact low_of_outs hout) (by rw [hmem2, hmem1]; exact high_of_outs hout)
      (fun _ h => by cases h)
    refine ⟨h4, ⟨_, primeEntry (rOf p original used st) ++ [1, 2], hlive, measure_lt p hpos hle (Nat.le_refl _),
      ?_, rfl, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩, hfin0⟩
    rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate
