module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Begin
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SpecPost

/-!
# A hashing pair, complete

`pairMCode_ok`: `beginM_ok`, then `Paired.finishCode` from
`Paired.finish_ok`, run from the state `beginM` left with the registers
of the pair's start (which is all `finish_ok` asks of its `initial` state
but its memory). `PairMPostW.outcome`: its outcome in terms of the
specification (as `Paired.PairPostW.outcome`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites accepted seedState seedBytes pairRegs
  pairWorkingRegs finishCode finish_ok PairPost PairPostW)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

theorem pairM_iff (sb ss off : Nat) (L : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (a j m : Nat) (w16 : Bool)
    (s : State) (Q : State → Prop) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pairM sb ss off L S a j m w16) s Q ↔
    WP isa (.seq (beginMCode L S sb ss a (a+1) j m (off+1024*a) (off+1024*(a+1)) w16) (finishCode w16)) s Q := by
  simp only [Impl.MlKem.AArch64.Hybrid.pairM, beginMCode, Paired.initialCode, finishCode, seqs,
    show [Instr.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23]=
      [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704]++[.logic .and .x .x6 .x22 .x23] from rfl]
  simp only [WP.seq_iff (M := isa),WP.block_append_iff (M := isa)]

structure PairMPostW (w16 : Bool) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (A B : Spec.Sha3.State) (p a b e st : Addr) (E : List Byte) (j m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWrites3 p a b st s.sp) s.mem t.mem
  left : CoeffsUpToW w16 t.mem a (accepted A 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted A 5)) (fun _=>0)
  reducedLeft : ReducedW (cw w16) t.mem a
  right : CoeffsUpToW w16 t.mem b (accepted B 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted B 5)) (fun _=>0)
  reducedRight : ReducedW (cw w16) t.mem b
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0)
  hash : stateAt t.mem st = hstate E (j + min 3 m) (dB S)
  ek : bytesAt t.mem e S.len = E

theorem pairMCode_ok {w16 : Bool} (L : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State}
    {p seed outA outB table e st : Addr} {E : List Byte} {sb ss a j m oa ob : Nat} (hS : SrcOk S)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h : Paired.BeginInput sb ss oa ob p seed outA outB table s)
    (hh : HashInput S p outA outB table e st s)
    (hb : ∀ k < m, k < 3 → 136 * (j + k) < S.len)
    (hash : stateAt s.mem st = hstate E j (dB S)) (hE : bytesAt s.mem e S.len = E)
    (h24 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) :
    WP isa (.seq (beginMCode L S sb ss a (a+1) j m oa ob w16) (finishCode w16)) s
      (PairMPostW w16 S (seedState s.mem seed a L.k) (seedState s.mem seed (a+1) L.k) p outA outB e st E j m s) := by
  refine WP.seq (WP.mono_syms (beginM_ok L S hS hss hsb h8b hoa hob h hh hb hash hE)
    fun u hu sy => ?_)
  let initial : State := { s with mem := u.mem }
  have hk : Keep pairWorkingRegs initial u :=
    let k := hu.keep.mono (rs' := pairWorkingRegs) (by decide)
    ⟨k.gpr, k.rd, k.wr, k.sp, k.vcs⟩
  refine WP.mono (finish_ok (initial := initial) hk (Frame.refl _ _) hu.saved hu.progress
    (by rw [sy]; exact h.symbol) hu.flag (hu.keep.get .x24) h24) fun t ht => ?_
  have fut : Frame (stepWrites p outA outB) u.mem t.mem := ht.frame
  have hSt : ∀ r ∈ stepWrites p outA outB, (stR st).Disjoint r := by
    intro r hr; simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hh.lay.dSP
    · exact hh.aS.symm
    · exact hh.bS.symm
  have hE' : ∀ r ∈ stepWrites p outA outB, (Region.mk e S.len).Disjoint r := by
    intro r hr; simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hh.lay.dEP
    · exact hh.aE.symm
    · exact hh.bE.symm
  refine ⟨⟨ht.keep.gpr, ht.keep.rd, ht.keep.wr, ht.keep.sp, ht.keep.vcs⟩, hu.frame.trans (fut.mono fun r hr => List.mem_append_left _ hr), ht.left,
    ht.reducedLeft, ht.right, ht.reducedRight, ht.status, ?_, ?_⟩
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fut hSt, hu.hash]
  · rw [VG.Proof.MlKem.bytesAt_frame fut hE' (by have := hS.lim; omega), hu.ek]

structure PairMOutcomeW (w16 : Bool) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (A B : List Byte) (p a b e st : Addr) (E : List Byte) (j m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWrites3 p a b st s.sp) s.mem t.mem
  reducedLeft : ReducedW (cw w16) t.mem a
  reducedRight : ReducedW (cw w16) t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAtW (cw w16) t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)
  hash : stateAt t.mem st = hstate E (j + min 3 m) (dB S)
  ek : bytesAt t.mem e S.len = E

theorem PairMPostW.outcome {w16 : Bool} {S : Impl.MlKem.AArch64.Hybrid.HSrc} {s t : State} {p seed a b e st : Addr} {E : List Byte} {i i' k n m : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairMPostW w16 S (seedState s.mem seed i k) (seedState s.mem seed i' k) p a b e st E n m s t) :
    PairMOutcomeW w16 S (seedBytes s.mem seed i k) (seedBytes s.mem seed i' k) p a b e st E n m s t := by
  have ra := Paired.accepted_result hk hk256 h.left
  have rb := Paired.accepted_result hk hk256 h.right
  refine ⟨h.keep,h.frame,h.reducedLeft,h.reducedRight,?_,?_,?_,h.hash,h.ek⟩
  · rcases ra with ⟨_,ha⟩|⟨_,ha⟩
    · exact Or.inr ha
    · exact Or.inl ha
  · rcases rb with ⟨_,hb⟩|⟨_,hb⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rw [h.status]
    rcases ra with ⟨la,ha⟩|⟨la,ha⟩ <;> rcases rb with ⟨lb,hb⟩|⟨lb,hb⟩ <;>
      simp [ha,hb,la,lb]

end VG.Proof.MlKem.AArch64.Hybrid
