module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Ends
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # A prime's search that asked for entropy or was exhausted

After the search and the count of its octets (`Mid`): the key search asks for
more entropy with the search's state; or the generation fails, and the key
search is exhausted or starts the next generation.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- How the key search goes on after the prime's search `r` from the progress
`st`: to the progress `st'`, with `e` this step's trace. -/
def NextPub (st : KeyProgress) (r : PrimeSearchResult) (st' : KeyProgress) (e : List Nat) : Prop :=
  (r.outcome = .exhausted ∧ st'.left = st.left - 1 ∧ st'.phase = .p ∧ e = primeEntry r) ∨
  (∃ c, r.outcome = .accepted c ∧ st.phase = .p ∧ st'.left = st.left ∧ phaseWord st'.phase = 1 ∧
    e = primeEntry r) ∨
  (∃ c pB, r.outcome = .accepted c ∧ st.phase = .q pB ∧ st'.left = st.left ∧ st'.phase = .p ∧
    e = primeEntry r ++ [1, 2])

/-- After a step that goes on: its status 4, and the loop state of the next
prime's search, of a lower measure. -/
structure Cont (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop where
  status : word t.mem p.F 80 = BitVec.ofNat 64 4
  next : ∃ st' e, GenLive p original (used + (rOf p original used st).used) st' t ∧
    genMeasure p (used + (rOf p original used st).used) st' < genMeasure p used st ∧
    tailOf p original used st =
      (tailOf p original (used + (rOf p original used st).used) st').consume (rOf p original used st).used e ∧
    st'.remaining = limitOf p.L p.eB ∧ NextPub st (rOf p original used st) st' e
  final : ∃ tr, final = (tailOf p original used st).consume used tr

/-- After a step: the next prime's search, or the key search ended with
`final`. -/
def Classified (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  Cont p original final used st t ∨ GenDone p original final t

theorem test_guard {s : State} {n : Nat} (hs : s.gpr .rcx = BitVec.ofNat 64 n) (h64 : n < 2 ^ 64) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      (eval .e t = some (decide (n = 0)) ∧ t.mem = s.mem) ∧ Keep [.rcx] s t := by
  have he : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == (0 : BitVec 64)) = decide (n = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rcx] ?_ rfl
  xrun [hs, eval, he]

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key9 {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.kp (9 * p.L) =
      Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) := by
  have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
  rwa [Nat.zero_mul, ← kp_zero] at this

/-- `fail status`: zeros at the key's buffer, and the key search ended with
`final`. -/
theorem fail_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0) (hz : keySearchBytes p.L final = List.replicate (9 * p.L) 0)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (fail status) s (GenDone p original final) := by
  have hf := h.input.cfacts
  unfold fail
  refine WP.seq (WP.mono (clearAll_ok h) fun w ⟨g, z, fr⟩ => ?_)
  obtain ⟨req, hw, hr⟩ := hreq
  refine finish_done g hstat hu hpr hs hr0 (z.trans hz.symm) ⟨req, ?_, hr⟩
  refine Eq.trans (fr.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
    (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
    (fun q hq => ?_) (by decide)) hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hf.kT.symm
  · exact h.state_frame.symm

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

/-- The search asked for more entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p original final used st u)
    (hax : u.gpr .rax = BitVec.ofNat 64 (rOf p original used st).status) {k a : Nat}
    (ho : (rOf p original used st).outcome = .entropy k a) :
    WP isa (.block [.store (field 10) .rax]) u (Classified p original final used st) := by
  have hf := hm.frame.input.cfacts
  have hs0 : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
  have hrem : (rOf p original used st).remaining = k := by
    simp only [PrimeSearchResult.remaining, ho]
  rw [hs0] at hax
  have hframe := hm.frame
  rw [hrem] at hframe
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_entropy (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
  have hfinal : final = ⟨.entropy ⟨st.left, st.phase, k⟩ a, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  refine WP.mono (storeStatus_ok hframe hax) fun t ⟨htm, k'⟩ => Or.inr ?_
  have hv : StateStores [] [(10, BitVec.ofNat 64 0)] := by
    constructor
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hg : GenFrame p original (used + (rOf p original used st).used) ⟨st.left, st.phase, k⟩ t :=
    hframe.setState hv htm k'.2.1 k'.2.2 (fun r _ => k'.gpr (by simp)) hframe.state.remaining
      hframe.state.phase hframe.state.left hframe.state.remaining_le hframe.state.left_lt
  obtain ⟨req, hw, hr⟩ := hm.req
  subst hfinal
  refine ⟨hg, ?_, ?_, ⟨req, ?_, ?_⟩⟩
  · rw [htm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide)]
    rfl
  · rw [htm, stores_key9 hframe hv, key_bytes, hm.low, hm.slot4, hm.slot5, hm.high]
    have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
      simp only [outBytes, ho]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [hout, keySearchBytes, List.replicate_append_replicate]
      congr 1; omega
    | q pB =>
      simp only [hout, keySearchBytes, List.append_assoc, List.replicate_append_replicate]
      congr 3; omega
  · rw [htm]; exact (stores_word hframe hv 3 (by decide)).trans hw
  · simp only [Spec.Entropy.Result.Requests, ho] at hr ⊢
    exact hr

/-- The search was exhausted, and so is the key search: its last generation. -/
theorem classify_last (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : st.left < 2) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- The search was exhausted: the next generation, from `p`. -/
theorem classify_next (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : ¬st.left < 2) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
      (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hv : StateStores [(5, BitVec.ofNat 64 (st.left - 1)), (0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 0)] [(10, (4 : BitVec 64))] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
    simp only [outBytes, ho]
  have hlt := hm.frame.state.left_lt
  have hle := hm.frame.used_le
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hm.slot5, hm.high,
      ← List.replicate_append_replicate]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => rfl
    | q pB => simp only [hout]
  obtain ⟨h4, hlive⟩ := cont_of (st' := ⟨st.left - 1, .p, limitOf p.L p.eB⟩) hm.frame hv htm hr hw hg rfl rfl rfl
    (Nat.le_refl _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm.frame.state.left_lt) hm.low hhigh5
    (fun _ h => by cases h)
  refine ⟨h4, ⟨_, primeEntry (rOf p original used st), hlive, ?_, ?_, rfl, .inl ⟨ho, rfl, rfl, rfl⟩⟩, hm.final⟩
  · unfold genMeasure
    dsimp only
    have hmul : (p.randLen - (used + (rOf p original used st).used)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate
