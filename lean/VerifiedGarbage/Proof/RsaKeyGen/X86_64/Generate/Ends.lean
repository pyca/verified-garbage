module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Step
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # How a step ends

Zeros at the whole key's buffer (`clearAll`); the end of the key search
(`finishWith`), to `GenDone`; and the start of the next prime's search,
to a loop state of a lower measure.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem setAll_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
      .mov .rdx (.reg .rcx), .shift .shl .rcx 3, .alu .add .rcx (.reg .rdx), .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L)] ∧
        Keep [.rax, .rcx, .rdx] s t := by
  have scr := h.scr
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 8) 8 := scr.ld (d := 8) (by decide)
  have hs12 : InRegions s.wr (p.F + BitVec.ofNat 64 96) 8 := scr.st (d := 96) (by decide)
  have hs13 : InRegions s.wr (p.F + BitVec.ofNat 64 104) 8 := scr.st (d := 104) (by decide)
  have h0 := h.header (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have h1 := h.header (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx, .rdx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl8, read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs12, hs13]

/-- `clearAll`: zeros at the whole key's buffer. -/
theorem clearAll_ok (h : GenFrame p original used st s) :
    WP isa clearAll s fun t => GenFrame p original used st t ∧
      Spec.Rsa.bytesAt t.mem p.kp (9 * p.L) = List.replicate (9 * p.L) 0 ∧
      Frame [cK p, p.frame] s.mem t.mem := by
  have hn := h.key_nowrap
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have hkr := h.key_region
  have h9 : BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L = BitVec.ofNat 64 (9 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]; congr 1; omega
  unfold clearAll
  refine WP.seq (WP.mono (setAll_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
  rw [h9] at w13
  refine WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega)) (by omega) (by omega)
    (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ⟨g2, bytes_zero z2, ?_⟩
  refine (f1.sub fun r hr => ?_).trans (f2.sub fun r hr => ?_)
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

end

/-- The state's word `j` through stores to the state and the frame. -/
theorem stores_word {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    (j : Nat) (hj : j < 7) :
    word (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.stp (8 * j) =
      frameValue sv j (word s.mem p.stp (8 * j)) := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  rw [← writeFrame_word _ _ _ hsb j (by omega)]
  exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
    (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact h.state_frame.symm) (by decide)

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    {j n : Nat} (hj : j * p.L + n ≤ 9 * p.L) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) (p.kp + BitVec.ofNat 64 (j * p.L)) n =
      Spec.Rsa.bytesAt s.mem (p.kp + BitVec.ofNat 64 (j * p.L)) n := by
  have hf := h.input.cfacts
  refine stores_bytes p s.mem (R := ⟨p.kp + BitVec.ofNat 64 (j * p.L), n⟩) hv ?_ ?_ (by have := hf.nK; simp; omega)
  · exact (hf.kT.symm.sub_right (slot_sub _ hj)).sub_left (Region.sub_prefix (by decide))
  · exact h.frame_key.sub_right (slot_sub _ hj)

/-- `finishWith status`: the key search ended with `final`. -/
theorem finish_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0)
    (hkey : Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith status)) s (GenDone p original final) := by
  refine WP.mono (finishWith_ok h hstat) fun t ⟨hm, k⟩ => ?_
  have hv : StateStores [(4, (0 : BitVec 64)), (5, (0 : BitVec 64))] [(10, BitVec.ofNat 64 status)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have h0 := h.state.remaining
  rw [hr0] at h0
  have hg : GenFrame p original u ⟨0, .p, 0⟩ t :=
    h.setState hv hm k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide)) h0 rfl rfl (Nat.zero_le _) (by decide)
  obtain ⟨req, hw, hr⟩ := hreq
  refine ⟨by rw [hu, hpr]; exact hg, ?_, ?_, ⟨req, ?_, hr⟩⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide), hs]
    rfl
  · rw [hm]
    have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
    rw [Nat.zero_mul, ← kp_zero] at this
    rw [this, hkey]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans hw

/-- The start of the next prime's search, for the progress `st'`: a loop
state, its status 4. -/
theorem cont_of {p : GenPublic} {original s t : State} {u : Nat} {st st' : KeyProgress}
    (h : GenFrame p original u st s) {sv : List (Nat × BitVec 64)}
    (hv : StateStores sv [(10, (4 : BitVec 64))])
    (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64)
    (hlow : Spec.Rsa.bytesAt s.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0)
    (hhigh : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hother : ∀ pB, st'.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    word t.mem p.F 80 = BitVec.ofNat 64 4 ∧ GenLive p original u st' t := by
  obtain ⟨hL1, -, -⟩ := h.len_valid
  have hg' := h.setState hv hm hr hw hg h0 h4 h5 hrem hlt
  refine ⟨?_, hg', ⟨?_, ?_, ?_⟩⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; decide) 10 (by decide)]
    rfl
  · have := stores_key h hv (j := 0) (n := 4 * p.L) (by omega)
    rw [Nat.zero_mul, ← kp_zero] at this
    rw [hm, this, hlow]
  · rw [hm, stores_key h hv (j := 5) (n := 4 * p.L) (by omega), hhigh]
  · intro pB hpB
    rw [hm, stores_key h hv (j := 4) (n := p.L) (by omega), hother pB hpB]

end VG.Proof.RsaKeyGen.X86_64.Generate
