module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState

/-! ### `Dsa.X86_64.Generation.TapeSlice`, which this module and modules that import it used -/

section

/-! # The next significant witness bytes are a disjoint slice of the random tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def PrimeParams.drawStart (P : PrimeParams) (used : Nat) : Nat := used + (P.drawBytes - P.len)
def PrimeParams.drawSlice (P : PrimeParams) (used : Nat) : List Byte := (P.rand.drop (P.drawStart used)).take P.len

theorem PrimeParams.slice_length (P : PrimeParams) {used : Nat} (h : used + P.drawBytes ≤ P.rand.length) :
    (P.drawSlice used).length = P.len := by
  simp only [PrimeParams.drawSlice, PrimeParams.drawStart, List.length_take, List.length_drop]
  have := P.lenDraw
  omega_using [h, this]

theorem PrimeState.slice_source {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : Src s P.B P.Z (off P.rp (P.drawStart used)) (P.drawSlice used) :=
  source_take (source_drop h.source (P.drawStart used)) P.len

theorem PrimeParams.slice_separate (P : PrimeParams) {used : Nat}
    (hroom : used + P.drawBytes ≤ P.rand.length) :
    ∀ i < (P.drawSlice used).length, ∀ j < (P.drawSlice used).length,
      off (off P.rp (P.drawStart used)) i ≠ off P.p j := by
  intro i hi j hj he
  rw [P.slice_length hroom] at hi hj
  have hs : P.drawStart used + i < P.rand.length := by
    dsimp only [PrimeParams.drawStart]; have := P.lenDraw; omega_using [hroom, hi, this]
  have ha : off (off P.rp (P.drawStart used)) i = off P.rp (P.drawStart used + i) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  apply P.tapeBuffer (off P.p j)
  · rw [← he, ha]
    apply (Region.contains_self P.rp P.rand.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.randMax; omega_using [hs, this])]
    exact hs
  · apply (Region.contains_self P.p P.len).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.lenDraw; have := P.drawMax; omega_arith)]
    exact hj

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.DrawCopy`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.PreparedFrame`, which only this module used -/

section

/-! # Preserve a prepared modulus across writes to separate byte buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem ready_of_work {s t : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} {extra : List Region}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hf : WorkFrame B rs extra s.mem t.mem)
    (hx : ∀ r ∈ extra, Region.Disjoint ⟨B, Z⟩ r)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = B)
    (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (ha : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], ∀ r ∈ rs,
      slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (he : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE) :
    ModulusReady t B Z w mi N := by
  have hn := h.good.scr.nowrap
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_using [this]
  have hword : ∀ d, d + 8 ≤ 128 → word t.mem B d = word s.mem B d := by
    intro d hd'
    exact hf.word_eq (fun r hr => Or.inl (Nat.le_trans hd' (hh r hr))) (by omega_using [hz, hd']) hn hx
  have hhdr : Hdr t.mem B w mi := by
    refine ⟨(hword _ (by decide)).trans h.good.hdr.hw,
      (hword _ (by decide)).trans h.good.hdr.hminv, ?_⟩
    intro j hj
    exact (hword _ (by unfold sArr; omega_using [hj])).trans (h.good.hdr.harr j hj)
  have hread : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], slot w j + 8 * w ≤ Z := by
    intro j hj
    have hj' : j ≤ aRm1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hs := VG.Proof.Rsa.slot_mono (w := w) hj'
    omega_using [hs, hd.x]
  have hval : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => hf.wv_eq (ha j hj) (hread j hj) hn hx
  refine ⟨⟨h.good.scr.congr hwr, hdi, hhdr⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.word_eq (fun r hr => by have := ha aN (by simp) r hr; have := hd.w4; omega_arith)
      (by have := hread aN (by simp); have := hd.w4; omega_arith) hn hx]
    exact h.inv
  · rw [hval aN (by simp)]; exact h.n
  · rw [hval aOne (by simp)]; exact h.one
  · rw [hval aR2 (by simp)]; exact h.r2
  · rw [hval aR1 (by simp)]; exact h.r1
  · rw [hval aRm1 (by simp)]; exact h.rm1
  · have hE := aE_fits hd
    refine ⟨?_, ?_⟩
    · rw [hf.wv_eq (fun r hr => by have := he r hr; omega_using [this]) (by omega_using [hE]) hn hx]
      exact h.exponent.e
    · rw [hf.word_eq (fun r hr => by have := he r hr; omega_using [this]) (by omega_using [hE]) hn hx]
      exact h.exponent.l

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Copy a complete draw and advance its tape cursor in verified code -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawCopy_ok {s : State} {B rp op : Addr} {Z w N drawBytes used : Nat} {mi : BitVec 64} {bs : List Byte}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hlen : 2 ≤ bs.length) (hld : bs.length ≤ drawBytes) (hmax : drawBytes ≤ 1024)
    (hrp : word s.mem B (8 * kRand) = rp) (hop : word s.mem B (8 * kOut) = op)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hdl : word s.mem B (8 * kLen) = BitVec.ofNat 64 drawBytes)
    (hll : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z (off rp (used + (drawBytes - bs.length))) bs)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hout : Region.Disjoint ⟨B, Z⟩ ⟨op, bs.length⟩)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off rp (used + (drawBytes - bs.length))) i ≠ off op j) :
    WP isa Impl.Dsa.X86_64.Generation.drawCopy s fun t =>
      ModulusReady t B Z w mi N ∧ Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + drawBytes) ∧
      WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_arith
  unfold Impl.Dsa.X86_64.Generation.drawCopy
  simp only [seqs]
  refine WP.seq (WP.mono (drawCopyArgs_ok h.good hd.z hld hrp hop hus hdl hll)
    fun u ⟨h15, hsi, hdi, hcx, hdx, hmu, ku⟩ => ?_)
  have hfu : Frm B [(8 * kUsed, 8)] s.mem u.mem := by
    rw [hmu]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kUsed) (by decide)) (by simp)
  have hsrcu := hsrc.congrK (fun x hx => hfu x (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    right; change 208 ≤ ofs B x; omega_arith)) ku
  have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := fun i hi => by rw [ku.2.2]; exact hwr i hi
  have hbu : ∀ i < bs.length, u.mem (off (off rp (used + (drawBytes - bs.length))) i) = bs.getD i 0 := by
    intro i hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hsrcu.val i hi
  refine WP.seq (WP.mono (copyBytes_ok ⟨hlen, by omega_arith⟩ hsi hdi hcx hdx hsrcu.rd hwu hbu hsep)
    fun v ⟨hbv, hfv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = v.mem) (by
    xrun [(kv.gpr (by decide) : v.gpr .r15 = u.gpr .r15).trans h15]) rfl)
    fun t ⟨⟨hdit, hmt⟩, kt⟩ => ?_
  have k := (ku.trans kv).trans kt
  have hfvt : WorkFrame B [] [⟨op, bs.length⟩] u.mem t.mem := by
    intro x hx _
    rw [hmt]
    apply hfv
    intro i hi he
    subst x
    apply hx ⟨op, bs.length⟩ (by simp)
    apply (Region.contains_self op bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64)]
    exact hi
  have hft : WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem :=
    hfu.work.trans (hfvt.mono (by simp))
  have hex : ∀ r ∈ [⟨op, bs.length⟩], Region.Disjoint ⟨B, Z⟩ r := by simpa using hout
  refine ⟨ready_of_work h hd hft hex k.2.2 hdit (by simp; decide) (by rng_disj) (by rng_disj),
    by rw [hmt]; exact hbv, ?_, hft, ?_⟩
  · rw [hfvt.word_eq (by simp) (by change 208 ≤ Z; omega_arith) h.good.scr.nowrap hex,
      hmu, word_writeW_self]
  · refine ⟨fun r hr => ?_, k.2⟩
    by_cases he : r = .rdi
    · subst r; exact hdit.trans h.good.rdi.symm
    · exact k.gpr (by revert hr he; cases r <;> decide)

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # A whole tape draw supplies the sampler and preserves all loop arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawBuffer_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.drawCopy) s fun t =>
      PrimeState P mi (used + P.drawBytes) t ∧
      SampleState P.B P.p P.Z P.w P.N mi (P.drawSlice used) t ∧
      WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlen := P.slice_length hroom
  have hs : Src s P.B P.Z (off P.rp (used + (P.drawBytes - (P.drawSlice used).length))) (P.drawSlice used) := by
    rw [hlen]; exact h.slice_source
  have hw : ∀ i < (P.drawSlice used).length, InRegions s.wr (off P.p i) 1 := by
    rw [hlen]; exact h.writable
  have hout : Region.Disjoint ⟨P.B, P.Z⟩ ⟨P.p, (P.drawSlice used).length⟩ := by
    rw [hlen]; exact P.bufferSeparate
  have hd := drawCopy_ok h.ready P.dims (by rw [hlen]; exact P.len2)
    (by rw [hlen]; exact P.lenDraw) P.drawMax h.rand h.ptr h.used h.draw (by rw [hlen]; exact h.len) hs hw hout (by simpa only [hlen, PrimeParams.drawStart] using P.slice_separate hroom)
  rw [hlen] at hd
  refine WP.mono hd fun t ⟨ht, hbytes, hused, hf, hk⟩ => ?_
  have hft : WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact hf x (fun r hmem => hx r (by
      simp only [List.mem_singleton] at hmem; subst r; simp [primeExtras])) hr
  have hzt : 256 ≤ P.Z := P.z256
  have hpt : PrimeState P mi (used + P.drawBytes) t := h.advance ht hused hft hk
    (by simp only [List.mem_singleton, forall_eq]; change 208 ≤ P.Z; omega_using [hzt])
    (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  refine ⟨hpt, ⟨ht, hpt.ptr, ?_, ?_, ?_⟩, hft, hk⟩
  · rw [hlen]; exact hpt.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => P.bufferOutside i (by rwa [hlen] at hi)⟩
    · obtain ⟨r, hr, hc⟩ := hpt.writable i (by rwa [hlen] at hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have hb := bytesAt_read t.mem P.p (n := P.len) (i := i) (by rwa [hlen] at hi)
      simpa only [hbytes] using hb
  · rw [hlen]; exact hpt.writable

end VG.Proof.Dsa.X86_64.Generation
