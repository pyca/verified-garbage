module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Exit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Hdr
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load

/-!
# DSA's probable-prime test on PPC64LE: correctness

`code_ok`: from the precondition (`CIn`, and the table's words and region,
`ConstsOk`), the entry (`entry_ok`), the candidate's load (`loadC_ok`), the
body (`body_ok`) and the exit (`exit_ok`) return the test's status, write
the octets read to `used`, keep every byte of `ws` but the saved registers
and the working space, and preserve what the calling convention asks.
`correct`: the contract's postcondition, under `abi.withConsts`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.Bignum (word off slot Frm Outside)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)

/-- The trial table. -/
abbrev K : List (String × List (BitVec 64)) := TrialTable32.consts

/-- `CIn` of the state without the table's region gives it of the state. -/
theorem CIn.ofStrip {bits : Nat} {σ : State} (h : CIn bits (stripConsts K σ)) : CIn bits σ :=
  ⟨h.spLo, List.mem_of_mem_take h.rd, h.wr, h.wR, h.wU, h.rU, h.sW, h.sR, h.sU, h.fw, h.fr, h.fu, h.size, h.odd,
    h.bl⟩

/-- A byte at offset `i` of `p` lies outside a region at offset `e`. -/
theorem not_in (p : Addr) {i e k : Nat} (h : i + 1 ≤ e ∨ e + k ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    ¬ (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint p h hi he _ (Region.contains_self _ _) hc

/-- A region at offset `d` of `ws` lies in `ws`. -/
theorem sub_ws {σ : State} {d n : Nat} (h : d + n ≤ (σ.gpr .r4).toNat * 8) :
    Region.Sub ⟨σ.gpr .r3 + BitVec.ofNat 64 d, n⟩ (cW σ) :=
  Offset.sub_base _ h

theorem table_held {σ : State} (hk : ConstsOk K 176 σ) {i : Nat} (hi : i < 1024) :
    σ.mem.readW (σ.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
  have := hk.2.1 _ List.mem_cons_self i (by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; exact hi)
  have hl : i < TrialTable32.packed.length := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; exact hi
  rw [this]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact VG.Proof.RsaKeyGen.TrialTable32.packed_entry hi

theorem table_rd {σ : State} (hk : ConstsOk K 176 σ) : (⟨σ.syms TrialTable32.symbol, 8192⟩ : Region) ∈ σ.rd := by
  have := hk.mem_rd (name := TrialTable32.symbol) (ws := TrialTable32.packed) List.mem_cons_self
  rwa [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at this

theorem consts_wr1 {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State} (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

theorem table_wr {σ : State} (hk : ConstsOk K 176 σ) :
    ∀ r ∈ σ.wr, Region.Disjoint ⟨σ.syms TrialTable32.symbol, 8192⟩ r := by
  have := consts_wr1 (name := TrialTable32.symbol) (ws := TrialTable32.packed) hk
  rwa [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at this

/-- What the function leaves. -/
structure COut (bits : Nat) (σ f : State) : Prop where
  abi : abiPreserved σ f
  r3 : f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  keeps : Proof.Dsa.ModPow.Keeps (σ.gpr .r3) (σ.gpr .r4).toNat (layout bits).scratch σ.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .r7) 1 = [BitVec.ofNat 64 ((σ.gpr .r6).toNat - rest.length)]

/-- The bytes of `ws` the test keeps. -/
def Kept (bits : Nat) (σ : State) (m : Mem) : Prop :=
  ∀ i, i < 8 * (σ.gpr .r4).toNat → i < 384 ∨ 384 + (552 - 384 + 8 * keyWords bits) ≤ i →
    m (σ.gpr .r3 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .r3 + BitVec.ofNat 64 i)

/-- After the entry and the candidate's load: the body's context, the saved
registers, and the bytes of `ws` kept. -/
theorem after_loadC {bits : Nat} (hb : Bits bits) {σ s₁ s₂ : State} (h : CIn bits σ) (hk : ConstsOk K 176 σ)
    (ep : EntryPost bits σ s₁) (sy₁ : s₁.syms = σ.syms)
    (hl : (arr s₂.mem (wsB σ) (words bits) 0 = Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .r3) ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s₁.mem s₂.mem) ∧
      Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17] s₁ s₂) (sy₂ : s₂.syms = s₁.syms) :
    BIn bits σ s₂ ∧ Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s₂.mem ∧ Kept bits σ s₂.mem := by
  obtain ⟨⟨c₂, o₂⟩, k₂⟩ := hl
  have hs := shape_of hb
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have hslot : slot (words bits) 0 + 8 * words bits ≤ 8 * keyWords bits := by
    simp only [slot, VG.Impl.Bignum.hdrBytes]; omega
  have f₁ : Frame [cW σ] σ.mem s₁.mem := ep.frame.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_ws (by simp only [saveOff, keyOff] at *; omega)⟩
  have f₂ : Frame [⟨wsB σ, 8 * keyWords bits⟩] s₁.mem s₂.mem := frame_outside o₂ hslot
  have f₂' : Frame [cW σ] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    rw [List.mem_singleton] at hr; subst hr; exact sub_ws (by simp only [keyOff] at *; omega)⟩
  have fW := f₁.trans f₂'
  have bin : BIn bits σ s₂ := by
    refine ⟨hb, h, (env_of hs h ep).keep k₂ (by decide), (hdr_of ep).keep fun d hd => ?_, c₂, fun i hi => ?_,
      by rw [k₂.rd, ep.rd]; exact table_rd hk, ?_, sy₂.trans sy₁, k₂.sp.trans ep.sp, k₂.rd.trans ep.rd,
      k₂.wr.trans ep.wr⟩
    · rw [hdrWords_eq] at hd
      refine Frm.word_eq (Frm.of_outside o₂ (List.mem_singleton_self _)) (fun r hr => ?_) ?_
      · rw [List.mem_singleton] at hr; subst hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        left; simp only [slot, VG.Impl.Bignum.hdrBytes]
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> omega
      · have := (env_of hs h ep).hs.nowrap
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> omega
    · rw [fW.readW (r := ⟨σ.syms TrialTable32.symbol, 8192⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact table_wr hk _ hW) (by decide)]
      exact table_held hk hi
    · simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      exact fW.bytes (R := cR σ) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.wR.symm)
        (by have := (σ.gpr .r6).isLt; exact Nat.le_of_lt this) hi
  refine ⟨bin, ep.svd.frame_in (lo := saveOff) (n := 168) savedSlots_in f₂ fun r hr => ?_, fun i hi hout => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (show saveOff + 168 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  simp only [keyOff] at hsz
  have e₁ : s₂.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = s₁.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    f₂ _ fun r hr hc => by
      rw [List.mem_singleton] at hr; subst hr
      exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  have e₀ : s₁.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    ep.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := saveOff) (by simp only [saveOff]; omega) (by omega) (by simp only [saveOff]; omega) hc
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  rw [e₁, e₀]

/-- The saved registers survive the body. -/
theorem saved_body {bits : Nat} {σ s t : State} (h : CIn bits σ) (bo : BOut bits σ s t)
    (sv : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem) :
    Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem := by
  have hsz := h.size
  have hfw := h.fw
  refine sv.frame_in (lo := saveOff) (n := 168) savedSlots_in bo.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (show saveOff + 168 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  · exact (h.sW.symm.sub_left (sub_ws (by simp only [saveOff, keyOff] at *; omega)))

/-- The body and the exit, from the body's context. -/
theorem tail_ok (Ri : RoundImpl) {bits : Nat} {σ s₂ : State} (h : CIn bits σ) (bin : BIn bits σ s₂)
    (sv₂ : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s₂.mem) (kept : Kept bits σ s₂.mem) :
    WP isa (.seq (body Ri.name Ri.code) exit) s₂ (COut bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  refine WP.seq (WP.mono (body_ok Ri bin) fun t bo => ?_)
  refine WP.mono (exit_ok h bo (saved_body h bo sv₂)) fun f xo => ⟨xo.abi, xo.r3, fun i hi hout => ?_, xo.used⟩
  -- A byte of `ws` outside the scratch range.
  simp only [layout, List.mem_singleton, forall_eq, saveOff, keyOff] at hout hsz
  have inW : (cW σ).Contains (σ.gpr .r3 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  have e₃ : f.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = t.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    xo.frame _ fun r hr hc => by rw [List.mem_singleton] at hr; subst hr; exact h.wU _ inW hc
  have e₂ : t.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = s₂.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    bo.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
      · exact h.sW _ hc inW
  rw [e₃, e₂, kept i hi hout]

theorem code_ok (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) {σ : State} (h : CIn bits σ)
    (hk : ConstsOk K 176 σ) : WP isa (code bits Ri.name Ri.code) σ (COut bits σ) := by
  have hs := shape_of hb
  unfold code
  refine WP.seq (WP.mono_syms (entry_ok hs h) fun s₁ ep sy₁ => ?_)
  refine WP.seq (WP.mono_syms (loadC_ok hs h ep) fun s₂ hl sy₂ => ?_)
  obtain ⟨bin, sv₂, kept⟩ := after_loadC hb h hk ep sy₁ hl sy₂
  exact tail_ok Ri h bin sv₂ kept

end VG.Proof.Dsa.PPC64LE.Prime
