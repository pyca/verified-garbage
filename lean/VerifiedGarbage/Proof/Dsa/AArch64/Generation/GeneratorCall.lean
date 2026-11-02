module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorCall
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract

/-! # Calling the generator stage, which leaves its status in the generation frame

The stage runs on the generation's scratch space, with the h tape; the
generation stores its result, 1 when it found valid parameters and 0
otherwise, as the status 1 or 3 of the seed attempt. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

/-- The generator search's result, by the stage's. -/
theorem generatorResult_stage (value q : Nat) (hs : List Nat) (rest : List Byte) :
    VG.Proof.Dsa.Generation.generatorResult value q hs rest =
      some (Proof.Dsa.GeneratorStage.stage value q hs, rest) := by
  unfold VG.Proof.Dsa.Generation.generatorResult Proof.Dsa.GeneratorStage.stage
  cases Spec.Dsa.generator value q hs with
  | none => rfl
  | some g => by_cases hv : Spec.Dsa.parametersValid ⟨value, q, g⟩ <;> simp [hv]

theorem GenerationGeometry.supported (p : GenerationGeometry) : Generator.Supported p.pLen := p.width

theorem GenerationGeometry.qLen_eq (p : GenerationGeometry) : Impl.Dsa.AArch64.Generator.qLen p.pLen = p.qLen := by
  rcases p.lengths with h | h | h <;> simp [h.1, h.2, Impl.Dsa.AArch64.Generator.qLen]

/-- The stage's arguments, from the frame. -/
theorem generatorCallArgs_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs p.geo.pLen)) s fun u =>
      u.gpr .x0 = p.geo.B ∧ u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) ∧
      u.gpr .x2 = p.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length ∧ u.mem = s.mem ∧
      Keep [.x0, .x1, .x2, .x3] s u := by
  have L := h.layout
  obtain ⟨V, R⟩ := h.rep
  have w5 : s.mem.readW (p.geo.F + BitVec.ofNat 64 40) 64 = p.geo.B :=
    (R.fr 5 (by decide)).trans ((h.slots 5 (by decide)).trans p.baseSlot)
  have w11 : s.mem.readW (p.geo.F + BitVec.ofNat 64 88) 64 = p.hs.ptr :=
    (R.fr 11 (by decide)).trans ((h.slots 11 (by decide)).trans p.hSlot)
  have w13 : s.mem.readW (p.geo.F + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 p.hs.bytes.length :=
    (R.fr 13 (by decide)).trans ((h.slots 13 (by decide)).trans p.hLengthSlot)
  have l40 := L.ld (d := 40) (n := 8) (by decide)
  have l88 := L.ld (d := 88) (n := 8) (by decide)
  have l104 := L.ld (d := 104) (n := 8) (by decide)
  simp only [off] at l40 l88 l104
  rw [← L.sp] at w5 w11 w13 l40 l88 l104
  have hu : BitVec.setWidth 64 (BitVec.ofNat 16 (usedBytes p.geo.pLen / 8)) = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) := by
    rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide
  have run : WP isa (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs p.geo.pLen)) s fun u =>
      u.gpr .x0 = p.geo.B ∧ u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) ∧
      u.gpr .x2 = p.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length ∧ u.mem = s.mem := by
    unfold Impl.Dsa.AArch64.Generation.generatorCallArgs
    brun [State.write, exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 88) (by decide),
      exec_ldrSp (off := 104) (by decide), l40, l88, l104, w5, w11, w13, hu]
  exact WP.mono (WP.keep [.x0, .x1, .x2, .x3] run
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide) rfl
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide +kernel)) fun u ⟨hu, hk⟩ =>
    ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2, hk⟩

/-- The stage's regions: the h tape; the scratch space. -/
def generatorCallRd (p : GenerationContext) : List Region := [⟨p.hs.ptr, p.hs.bytes.length⟩]

def generatorCallWr (p : GenerationContext) : List Region := [⟨p.geo.B, usedBytes p.geo.pLen⟩]

theorem usedBytes_words {pLen : Nat} (h : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    (BitVec.ofNat 64 (usedBytes pLen / 8)).toNat * 8 = usedBytes pLen ∧
      usedBytes pLen ≤ 8 * (BitVec.ofNat 64 (usedBytes pLen / 8)).toNat := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the call itself leaves, before its result is stored. -/
structure GeneratorCalled (p : GenerationContext) (value q : Nat) (s u t : State) : Prop where
  rd : t.rd = u.rd
  wr : t.wr = u.wr
  sp : t.sp = p.geo.F
  status : (t.gpr .x0).setWidth 32 = BitVec.ofNat 32
    (if (Proof.Dsa.GeneratorStage.stage value q
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)).isSome then 1 else 0)
  packed : ∀ a, Proof.Dsa.GeneratorStage.stage value q
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) = some a →
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
      Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a
  keeps : Proof.Dsa.ModPow.Keeps p.geo.B (usedBytes p.geo.pLen / 8)
    (Impl.Dsa.AArch64.Generator.layout p.geo.pLen).scratch s.mem t.mem
  frame : Frame [⟨p.geo.B, usedBytes p.geo.pLen⟩, below p.geo.F 272] s.mem t.mem

/-- What the callee starts from: its precondition, regions of the caller's,
and the values it reads. -/
structure GeneratorEntry (p : GenerationContext) (value qval : Nat) (u : State) : Prop where
  pre : (Generator.contract p.geo.pLen).pre (u.callEntry.withRegions (generatorCallRd p) (generatorCallWr p))
  reads : Covers (generatorCallRd p ++ generatorCallWr p) (u.rd ++ u.wr)
  writes : Covers (generatorCallWr p) u.wr
  pv : Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = value
  qv : Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = qval
  tape : Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length = p.hs.bytes

theorem generatorCall_entry {p : GenerationContext} {W : Nat → BitVec 64} {s u : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    (h0 : u.gpr .x0 = p.geo.B) (h1 : u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8))
    (h2 : u.gpr .x2 = p.hs.ptr) (h3 : u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length) (hm : u.mem = s.mem)
    (hsp : u.sp = p.geo.F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    GeneratorEntry p value qval u := by
  have hb := p.geo.supported
  have hn := p.hs.size
  have qq := p.geo.qLen_eq
  have hw := usedBytes_words p.geo.width
  have hl : (BitVec.ofNat 64 p.hs.bytes.length).toNat = p.hs.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  have pv : Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = value := by
    unfold Proof.Dsa.GeneratorStage.pAt Proof.Dsa.GeneratorStage.numberAt
    rw [hm]
    exact (congrArg Spec.Dsa.decodeBE bp).trans (VG.Proof.Dsa.decodeBE_encodeBE pfit)
  have qv : Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = qval := by
    unfold Proof.Dsa.GeneratorStage.qAt Proof.Dsa.GeneratorStage.numberAt
    rw [hm]
    change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q)
      (Impl.Dsa.AArch64.Generator.qLen p.geo.pLen)) = qval
    rw [qq]
    exact (congrArg Spec.Dsa.decodeBE bq).trans (VG.Proof.Dsa.decodeBE_encodeBE qfit)
  have tapeV : Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length = p.hs.bytes := by rw [hm]; exact h.hs.bytes
  -- The callee's regions are the generation's.
  have cW : Covers (generatorCallWr p) u.wr := by
    obtain ⟨⟨B₀, o, L₀, hmem, hbase, hle, _⟩, _⟩ := h.scratch
    rw [hwr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, hmem, o, hbase, hle⟩
  have cR : Covers (generatorCallRd p) (u.rd ++ u.wr) := by
    rw [hrd, hwr]; exact h.hs.cover
  have frameBelow : Region.Disjoint ⟨p.geo.F, frameBytes⟩ (below p.geo.F 288) :=
    Offset.base_disjoint_below p.geo.F (by decide)
  have pre : (Generator.contract p.geo.pLen).pre
      (u.callEntry.withRegions (generatorCallRd p) (generatorCallWr p)) := by
    sig_pre [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    sig_and_intros
    all_goals try simp only [h0, h1, h2, h3, hsp, hl, hw.1, generatorCallRd, generatorCallWr]
    · exact p.geo.callSize
    · exact p.hs.arena.symm
    · exact p.geo.callArena
    · exact p.hs.callStack.symm
    · exact p.geo.arenaBound
    · exact p.hs.bound
    · exact hw.2
    · exact p.hsChunks
    · rw [pv]; exact domain.odd
    · rw [pv]
      exact (VG.Proof.Dsa.bitLength_iff_bounds (by rcases domain.width with h | h | h <;> omega)).mpr
        ⟨domain.lower, domain.upper⟩
    · rw [qv]; exact qpos
    · rw [pv, qv, hm]; exact be
  exact ⟨pre, cR.append_left cW.right, cW, pv, qv, tapeV⟩

theorem generatorCall_call_ok (G : GeneratorStage) {p : GenerationContext} {W : Nat → BitVec 64} {s u : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    (h0 : u.gpr .x0 = p.geo.B) (h1 : u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8))
    (h2 : u.gpr .x2 = p.hs.ptr) (h3 : u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length) (hm : u.mem = s.mem)
    (hsp : u.sp = p.geo.F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    WP isa (G.run p.geo.pLen) u (GeneratorCalled p value qval s u) := by
  have hb := p.geo.supported
  have hd := G.depth p.geo.pLen
  have hn := p.hs.size
  have qq := p.geo.qLen_eq
  have hl : (BitVec.ofNat 64 p.hs.bytes.length).toNat = p.hs.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have E := generatorCall_entry h value qval domain qfit qpos bp be bq h0 h1 h2 h3 hm hsp hrd hwr
  have pv := E.pv
  have qv := E.qv
  have tapeV := E.tape
  refine WP.callF (G.verified p.geo.pLen hb).1 E.pre E.reads E.writes ?_
    (by have := hd; omega)
  intro t hrd' hwr' hsp' hf _ hpost
  sig_post [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    at hpost
  simp only [h0, h1, h2, h3, hl] at hpost
  rw [pv, qv] at hpost
  obtain ⟨hr, hkeeps, hpk⟩ := hpost
  have cands : Proof.Dsa.GeneratorStage.candidates p.geo.pLen (Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length) =
      (Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE := by
    rw [tapeV]; rfl
  rw [cands] at hr hpk
  refine ⟨hrd', hwr', hsp'.trans hsp, ?_, fun a ha => ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [hr, BitVec.toNat_ofNat]
    split <;> rfl
  · have := hpk a ha
    rw [← qq]
    exact this
  · rw [← hm]
    have := hkeeps
    rw [show (BitVec.ofNat 64 (usedBytes p.geo.pLen / 8)).toNat = usedBytes p.geo.pLen / 8 by
      rcases p.geo.width with hw' | hw' | hw' <;> rw [hw'] <;> decide] at this
    exact this
  · rw [← hm]
    refine Frame.sub hf fun r hr => ?_
    simp only [generatorCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · rw [hsp]
      exact ⟨below p.geo.F 272, by simp, below_sub (by omega) (by decide)⟩

theorem exec_addImm_w0 {s : State} {d n : Reg} :
    exec (.addImm .w d n 0) s = some (s.write .w d ((s.gpr n).setWidth 32)) := by
  simp [exec, State.read, Size.bits]

/-- The status, 3 − 2 r for the stage's result r, stored in word 19. -/
theorem generatorCallStatus_ok {t : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t F S) (R : Rep t.mem F S V W) {b : Bool}
    (hx0 : (t.gpr .x0).setWidth 32 = BitVec.ofNat 32 (if b then 1 else 0)) :
    WP isa (.block Impl.Dsa.AArch64.Generation.generatorCallStatus) t fun t' =>
      Lay t' F S ∧ Rep t'.mem F S V (upd W 19 (BitVec.ofNat 64 (if b then 1 else 3))) ∧
      Frame [⟨F, frameBytes⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hz : ((BitVec.ofNat 32 (if b then 1 else 0)).setWidth 64 : BitVec 64) = BitVec.ofNat 64 (if b then 1 else 0) := by
    cases b <;> decide
  have h3 : BitVec.setWidth 64 (BitVec.ofNat 16 3) = (3 : BitVec 64) := by decide
  have hs : (3 : BitVec 64) - BitVec.ofNat 64 (if b then 1 else 0) - BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (if b then 1 else 3) := by cases b <;> decide
  have s152 : InRegions t.wr (t.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.st (d := 152) (n := 8) (by decide)
  have run : WP isa (.block Impl.Dsa.AArch64.Generation.generatorCallStatus) t
      fun t' => t'.mem = t.mem.writeW (off F (8 * 19)) (BitVec.ofNat 64 (if b then 1 else 3)) := by
    unfold Impl.Dsa.AArch64.Generation.generatorCallStatus
    brun [exec_addImm_w0, State.write, exec_storeSp (off := 152) (by decide), s152, hx0, hz, h3, hs]
    rw [L.sp]
  refine WP.mono (WP.keep [.x0, .x3] run (by decide)) fun t' ⟨hm, kt⟩ => ?_
  have Rt : Rep t'.mem F S V (upd W 19 (BitVec.ofNat 64 (if b then 1 else 3))) := hm ▸ R.wf L.geo (by decide) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) kt.sp kt.wr, Rt, ?_, kt.rd, kt.wr⟩
  rw [hm]
  exact (Frame.refl _ _).writeW List.mem_cons_self _ (cF F (by decide))

theorem generatorCall_ok (G : GeneratorStage) {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorCall G.run p.geo.pLen) s
      (SeedFinished p W (VG.Proof.Dsa.Generation.generatorResult value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop used)) s) := by
  have L := h.layout
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.generatorCall
  refine WP.seq (WP.mono (generatorCallArgs_ok h) fun u ⟨h0, h1, h2, h3, hm, ku⟩ => ?_)
  have hsp : u.sp = p.geo.F := ku.sp.trans L.sp
  refine WP.seq (WP.mono (generatorCall_call_ok G h value qval domain qfit qpos bp be bq h0 h1 h2 h3 hm hsp
    ku.rd ku.wr) fun t C => ?_)
  -- The frame and the hash workspace are as they were.
  have hashKept : ∀ o < oRsa, t.mem (off p.geo.hash o) = s.mem (off p.geo.hash o) := by
    intro o ho
    have c8 : VG.Impl.Dsa.Generation.Layout.hash = 16384 := rfl
    have c9 : oRsa = 8192 := rfl
    have hw8 : 8 * (usedBytes p.geo.pLen / 8) = usedBytes p.geo.pLen := by
      rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide
    have hhb : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.geo.pLen := p.geo.small_bound (by decide) (by decide)
    have k := C.keeps (VG.Impl.Dsa.Generation.Layout.hash + o) (by omega) (by
      intro r hr
      have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hw | hw | hw <;> omega
      have qn : Impl.Dsa.AArch64.Generator.qLen p.geo.pLen ≤ 32 := by
        unfold Impl.Dsa.AArch64.Generator.qLen; split <;> omega
      simp only [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [parent, g, packed, Impl.Dsa.AArch64.Generator.spill,
          VG.Impl.Dsa.Generation.Layout.control, arithmetic, domainCheck, Impl.Dsa.Layout.activeBytes,
          Impl.Dsa.AArch64.Generator.spillBytes, Impl.Dsa.Layout.usedBytes, arithmeticBytes] <;> omega)
    simpa only [GenerationGeometry.hash, off, BitVec.add_assoc, BitVec.ofNat_add] using k
  have frameKept : ∀ k < nW, word t.mem p.geo.F (8 * k) = W k := by
    intro k hk
    rw [← R.fr k hk]
    refine C.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    have hf : Region.Sub ⟨off p.geo.F (8 * k), 8⟩ ⟨p.geo.F, frameBytes⟩ :=
      Offset.sub_base _ (by have : nW = 34 := rfl; have : frameBytes = 272 := rfl; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.geo.frameArena.sub_left hf
    · exact p.geo.frame_below.sub_left hf
  have Rt : Rep t.mem p.geo.F p.geo.hash V W :=
    ⟨fun o ho => (hashKept o ho).trans (R.scr o ho), frameKept⟩
  have Lt : Lay t p.geo.F p.geo.hash := lay_of_rep L R Rt rfl (C.sp.trans L.sp.symm) (C.wr.trans ku.wr)
  let res := Proof.Dsa.GeneratorStage.stage value qval
    ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)
  refine WP.mono (generatorCallStatus_ok Lt Rt (b := res.isSome) C.status) fun t' ⟨Lt', Rt', ft', rdt', wrt'⟩ => ?_
  have hframe : Frame p.changed s.mem t'.mem := by
    refine (Frame.sub C.frame fun r hr => ?_).trans (ft'.mono (by simp [GenerationContext.changed]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩
    · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩
  have hrd : t'.rd = s.rd := rdt'.trans (C.rd.trans ku.rd)
  have hwr : t'.wr = s.wr := wrt'.trans (C.wr.trans ku.wr)
  have mem := h.frame Lt' ⟨V, Rt'⟩ (fun k hk => by
    have : k ≠ 19 := by
      simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [upd, this]) hframe hrd hwr
  refine ⟨_, used, mem, hu, by simpa [upd] using h16, fun k hk => by simp [upd, searchSlots_not_status hk],
    ?_, hframe, hrd, hwr⟩
  rw [generatorResult_stage]
  change SeedOutcome p (some (res, p.rand.bytes.drop used)) _ used t'
  cases hres : res with
  | none =>
    exact Or.inr (Or.inl ⟨by simp [upd], rfl⟩)
  | some a =>
    refine Or.inr (Or.inr ⟨by simp [upd], a, rfl, ?_⟩)
    rw [VG.Proof.Dsa.Generation.frame_bytesAt ft' (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact (p.geo.frame_part (p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen) (by decide)
        (by rcases p.geo.lengths with h | h | h <;> rw [h.1, h.2] <;> decide))).symm) (by
        rcases p.geo.lengths with h | h | h <;> rw [h.1, h.2] <;> decide)]
    exact C.packed a hres

end VG.Proof.Dsa.AArch64.Generation
