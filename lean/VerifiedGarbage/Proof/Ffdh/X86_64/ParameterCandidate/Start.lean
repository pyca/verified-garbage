module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! ### `Ffdh.X86_64.ParameterCandidate.Entry`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: save the ABI arguments and registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Domain (save)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  ((((((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW
    (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW
    (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * oOut)) (s.gpr .rdi)).writeW
    (off B (8 * oLen)) (s.gpr .rsi)).writeW (off B (8 * oUsedP)) (s.gpr .rdx)).writeW
    (off B (8 * oBits)) (s.gpr .rcx)).writeW (off B (8 * oGen)) ((s.gpr .r8).setWidth 32 |>.setWidth 64)).writeW
    (off B (8 * oRandStart)) (s.gpr .r9)).writeW (off B (8 * oRandPtr)) (s.gpr .r9)).writeW
    (off B (8 * oRandLeft)) (stackArg s 0)).writeW (off B (8 * oUsed)) (0#64)).writeW
    (off B (8 * oStatus)) (0#64))

private def entryValue (s : State) (B : Addr) (j : Nat) : BitVec 64 :=
  if j = 19 then 0#64 else
  if j = 14 then 0#64 else
  if j = 13 then stackArg s 0 else
  if j = 12 then s.gpr .r9 else
  if j = 11 then s.gpr .r9 else
  if j = 10 then ((s.gpr .r8).setWidth 32 |>.setWidth 64) else
  if j = 9 then s.gpr .rcx else
  if j = 8 then s.gpr .rdx else
  if j = 7 then s.gpr .rsi else
  if j = 6 then s.gpr .rdi else
  if j = 5 then s.gpr .r15 else
  if j = 4 then s.gpr .r14 else
  if j = 3 then s.gpr .r13 else
  if j = 2 then s.gpr .r12 else
  if j = 1 then s.gpr .rbp else
  if j = 0 then s.gpr .rbx else
  word s.mem B (8 * j)

private theorem header_word (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat}
    (hi : i < 32) (hj : j < 32) :
    word (m.writeW (off B (8 * i)) v) B (8 * j) = if j = i then v else word m B (8 * j) := by
  by_cases he : j = i
  · subst he
    rw [ite_eq_left rfl]
    exact word_writeW_self _ _ _ _
  · rw [ite_eq_right he]
    exact hdrStore_hdr _ _ _ hi hj (Ne.symm he)

private theorem entryMem_word (s : State) (B : Addr) {j : Nat} (hj : j < 32) :
    word (entryMem s B) B (8 * j) = entryValue s B j := by
  unfold entryMem
  rw [header_word _ _ _ (i := oStatus) (by decide) hj,
    header_word _ _ _ (i := oUsed) (by decide) hj,
    header_word _ _ _ (i := oRandLeft) (by decide) hj,
    header_word _ _ _ (i := oRandPtr) (by decide) hj,
    header_word _ _ _ (i := oRandStart) (by decide) hj,
    header_word _ _ _ (i := oGen) (by decide) hj,
    header_word _ _ _ (i := oBits) (by decide) hj,
    header_word _ _ _ (i := oUsedP) (by decide) hj,
    header_word _ _ _ (i := oLen) (by decide) hj,
    header_word _ _ _ (i := oOut) (by decide) hj,
    header_word _ _ _ (i := 5) (by decide) hj,
    header_word _ _ _ (i := 4) (by decide) hj,
    header_word _ _ _ (i := 3) (by decide) hj,
    header_word _ _ _ (i := 2) (by decide) hj,
    header_word _ _ _ (i := 1) (by decide) hj,
    header_word _ _ _ (i := 0) (by decide) hj]
  rfl

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧ word m B (8 * 1) = s.gpr .rbp ∧ word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧ word m B (8 * 4) = s.gpr .r14 ∧ word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * oOut) = s.gpr .rdi ∧ word m B (8 * oLen) = s.gpr .rsi ∧
    word m B (8 * oUsedP) = s.gpr .rdx ∧ word m B (8 * oBits) = s.gpr .rcx ∧
    word m B (8 * oGen) = ((s.gpr .r8).setWidth 32 |>.setWidth 64) ∧
    word m B (8 * oRandStart) = s.gpr .r9 ∧ word m B (8 * oRandPtr) = s.gpr .r9 ∧
    word m B (8 * oRandLeft) = stackArg s 0 ∧ word m B (8 * oUsed) = 0 ∧ word m B (8 * oStatus) = 0 ∧
    Outside B 0 160 s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change word (entryMem s B) B (8 * 0) = _
    simpa [entryValue] using entryMem_word s B (j := 0) (by decide)
  · change word (entryMem s B) B (8 * 1) = _
    simpa [entryValue] using entryMem_word s B (j := 1) (by decide)
  · change word (entryMem s B) B (8 * 2) = _
    simpa [entryValue] using entryMem_word s B (j := 2) (by decide)
  · change word (entryMem s B) B (8 * 3) = _
    simpa [entryValue] using entryMem_word s B (j := 3) (by decide)
  · change word (entryMem s B) B (8 * 4) = _
    simpa [entryValue] using entryMem_word s B (j := 4) (by decide)
  · change word (entryMem s B) B (8 * 5) = _
    simpa [entryValue] using entryMem_word s B (j := 5) (by decide)
  · change word (entryMem s B) B (8 * 6) = _
    simpa [entryValue] using entryMem_word s B (j := 6) (by decide)
  · change word (entryMem s B) B (8 * 7) = _
    simpa [entryValue] using entryMem_word s B (j := 7) (by decide)
  · change word (entryMem s B) B (8 * 8) = _
    simpa [entryValue] using entryMem_word s B (j := 8) (by decide)
  · change word (entryMem s B) B (8 * 9) = _
    simpa [entryValue] using entryMem_word s B (j := 9) (by decide)
  · change word (entryMem s B) B (8 * 10) = _
    simpa [entryValue] using entryMem_word s B (j := 10) (by decide)
  · change word (entryMem s B) B (8 * 11) = _
    simpa [entryValue] using entryMem_word s B (j := 11) (by decide)
  · change word (entryMem s B) B (8 * 12) = _
    simpa [entryValue] using entryMem_word s B (j := 12) (by decide)
  · change word (entryMem s B) B (8 * 13) = _
    simpa [entryValue] using entryMem_word s B (j := 13) (by decide)
  · change word (entryMem s B) B (8 * 14) = _
    simpa [entryValue] using entryMem_word s B (j := 14) (by decide)
  · change word (entryMem s B) B (8 * 19) = _
    simpa [entryValue] using entryMem_word s B (j := 19) (by decide)
  · unfold m entryMem
    repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem candidateEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 20, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(oOut, s.gpr .rdi), (oLen, s.gpr .rsi), (oUsedP, s.gpr .rdx), (oBits, s.gpr .rcx),
        (oGen, ((s.gpr .r8).setWidth 32 |>.setWidth 64)), (oRandStart, s.gpr .r9)] ∧
      word t.mem B (8 * oRandPtr) = s.gpr .r9 ∧ word t.mem B (8 * oRandLeft) = stackArg s 0 ∧
      word t.mem B (8 * oUsed) = 0 ∧ word t.mem B (8 * oStatus) = 0 ∧
      Outside B 0 160 s.mem t.mem ∧ Keep [.rax, .r10, .r8, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) 16) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .r8, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold entry save
      simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      dsimp only [VG.Impl.Rsa.X86_64.Crt.stk, stackArgAddr] at ha ⊢
      xrun [State.ea, ws, hdrOff, stackArg, stackArgAddr, hB',
        hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
        hw oOut (by decide), hw oLen (by decide), hw oUsedP (by decide), hw oBits (by decide), hw oGen (by decide),
        hw oRandStart (by decide), hw oRandPtr (by decide), hw oRandLeft (by decide), hw oUsed (by decide),
        hw oStatus (by decide), ha 1 (by decide), ha 0 (by decide)]
      rfl) rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hL, hU, hBits, hG, hR, hPtr, hLeft, hUsed, hStatus, hf⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hO hL hU hBits hG hR hPtr hLeft hUsed hStatus hf
  refine ⟨hdi, ?_, ?_, hPtr, hLeft, hUsed, hStatus, hf, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hO, hL, hU, hBits, hG, hR]

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: initialize the retained input state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (saved)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

def candidateOfState (s : State) : CandidateP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .rsi).toNat, (s.gpr .rcx).toNat,
    ((s.gpr .r8).setWidth 32).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r9, pcRand s, s.gpr .rsp⟩

theorem candidateEntry_base {s : State} (c : PcCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.ParameterCandidate.entry) s fun t =>
      CandidateTape (candidateOfState s) 0 t ∧ t.gpr .rdi = (candidateOfState s).B ∧
      word t.mem (candidateOfState s).B (8 * oStatus) = 0 ∧
      InScr (candidateOfState s).B (candidateOfState s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (candidateOfState s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  refine WP.mono (candidateEntry_ok rfl (fun i hi => c.scr.st (by omega_using [hi, c.room])) c.args)
    fun t ⟨hd, hsaved, hh, hptr, hleft, hused, hstatus, hf, k⟩ => ?_
  have hframe : InScr (candidateOfState s).B (candidateOfState s).Z s.mem t.mem :=
    InScr.of_outside hf (by dsimp only [candidateOfState]; omega_using [c.room])
  have hsp : t.gpr .rsp = (candidateOfState s).sp := k.gpr (by decide)
  have hbase : CandidateBase (candidateOfState s) t := by
    refine ⟨c.bits1, c.bits2, c.len, c.gen, ?_, c.room, c.scr.congr k.2.2,
      ⟨fun i hi => by rw [k.2.2]; exact c.out.wr i hi, c.out.sep⟩, c.usedMem.congr k.2.2,
      ⟨fun i hi => by rw [k.2.2]; exact c.used.wr i hi, c.used.sep⟩,
      c.rand.congrK hframe k, ?_, c.outUsed, hsp, c.stackSize, c.stackScr.symm, ?_, ?_⟩
    · change (pcRand s).length < 2 ^ 64
      rw [bytesAt_length]
      exact (stackArg s 0).isLt
    · change Apart (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .r9) (pcRand s).length
      rw [bytesAt_length]
      exact c.outRand
    · intro i hi
      change i < (pcRand s).length at hi
      apply c.stackRand.symm
      have hlen : (pcRand s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
      exact Offset.contains_base _ (by omega_using [hi, hlen]) (by omega_using [hi, hlen, (stackArg s 0).isLt])
    · have hg : BitVec.ofNat 64 ((s.gpr .r8).setWidth 32).toNat = ((s.gpr .r8).setWidth 32).setWidth 64 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      simpa only [CandidateP.headers, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq, hg] using hh
  refine ⟨⟨hbase, by omega_using [], ?_, ?_, hused⟩, hd, hstatus, hframe, hsaved, k.mono (by decide)⟩
  · simpa only [candidateOfState, off, BitVec.ofNat_toNat, BitVec.add_zero] using hptr
  · simpa only [candidateOfState, bytesAt_length, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hleft

end VG.Proof.Ffdh.X86_64.ParameterCandidate
