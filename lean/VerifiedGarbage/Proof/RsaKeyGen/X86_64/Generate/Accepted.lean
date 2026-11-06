module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Branches
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # A generation exhausted, or a prime accepted

`exhaustedGen`: the last generation, or the next. A prime accepted: the key
search is exhausted if it read nothing; `q` next after `p`; after `q`, the
key, which ends the key search, or, for a `d` too small, both primes again.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- One generation fewer, and the next prime's search from `p`. -/
theorem dec_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hax : s.gpr .rax = p.stp)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 st.left) (hl : 2 ≤ st.left) :
    WP isa (.block ([.alu .sub .rcx (.imm 1), .store (stw 5) .rcx] ++ nextPrime 0)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
        (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, (4 : BitVec 64))] ∧
        Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr p.stp 8 := by simpa only [off, BitVec.add_zero] using sst.st (d := 0) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7 h11
  have hlt := h.state.left_lt
  have hsub : BitVec.ofNat 64 st.left - (1 : BitVec 64) = BitVec.ofNat 64 (st.left - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show st.left - 1 < 2 ^ 64 by omega)]
    omega
  have hnF : p.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hnS : p.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 160) :
      (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 d) 64 =
        s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨p.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := p.frame)
      (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact h.state_frame) (by decide)
  have hk7 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 56) 64 =
      p.stp := fun v => (hkeep v 56 (by decide)).trans h7
  have hk11 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 88) 64 =
      BitVec.ofNat 64 (limitOf p.L p.eB) := fun v => (hkeep v 88 (by decide)).trans h11
  have h0 : (BitVec.ofNat 32 0).setWidth 64 = BitVec.ofNat 64 0 := by decide
  have h4 : (4 : BitVec 32).setWidth 64 = (4 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl11, hs10, hs0, hs4, hs5, hk7, hk11, hax, hcx, hsub, h0, h4]

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- `exhaustedGen`: the key search exhausted, or the next generation. -/
theorem classify_exhausted (hm : Mid p original final used st u)
    (ho : (rOf p original used st).outcome = .exhausted) :
    WP isa exhaustedGen u (Classified p original final used st) := by
  unfold exhaustedGen
  refine WP.seq (WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hax, hcx, hmem⟩, k⟩ => ?_)
  have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
  refine WP.ite (decide (st.left < 2)) hb (fun hl => ?_) (fun hl => ?_)
  · exact WP.mono (classify_last hv ho (of_decide_eq_true hl)) fun _ h => Or.inr h
  · have hl' := of_decide_eq_false hl
    refine WP.mono (dec_ok hv.frame hax hcx (by show 2 ≤ st.left; omega)) fun t ⟨htm, k2⟩ => Or.inl ?_
    exact classify_next hv ho hl' htm k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))

theorem drop_lt {rest : List Byte} {n : Nat} (h0 : 0 < n) (hn : n ≤ rest.length) :
    (rest.drop n).length < rest.length := by
  rw [List.length_drop]; omega

theorem measure_lt (p : GenPublic) {used n : Nat} {st st' : KeyProgress} (h0 : 0 < n)
    (hn : used + n ≤ p.randLen) (hl : st'.left ≤ st.left) :
    genMeasure p (used + n) st' < genMeasure p used st := by
  unfold genMeasure
  have hmul : (p.randLen - (used + n) + 1) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- A prime accepted having read nothing: the key search is exhausted. -/
theorem classify_none (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (h0 : (rOf p original used st).used = 0) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_accepted_none (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by show ¬(List.drop (rOf p original used st).used _).length < _; rw [h0, List.drop_zero]; omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- `p` accepted: `q` next. -/
theorem classify_p (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .p) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 1)]) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (drop_lt hpos hrest) hph
  have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 1)]
      [(10, (4 : BitVec 64))] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hs5, hm.high,
      ← List.replicate_append_replicate]
  obtain ⟨h4, hlive⟩ := cont_of (st' := ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩) hm.frame hv htm
    hr hw hg rfl rfl hm.frame.state.left (Nat.le_refl _) hm.frame.state.left_lt hm.low hhigh5 (fun pB h => by
      cases h; exact hs4)
  refine ⟨h4, ⟨_, primeEntry (rOf p original used st), hlive, measure_lt p hpos hle (Nat.le_refl _), ?_, rfl,
    .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩, hm.final⟩
  rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate
