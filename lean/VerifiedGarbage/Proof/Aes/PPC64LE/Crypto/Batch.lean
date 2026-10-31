module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Rounds
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the outer loops reuse this proof for eight blocks and for one block.
/-! # POWER8 AES batch composition -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (batchRegs breg key mask byteMask counterWord counterMask counterControl data)

theorem rewind_ok (ctr : Bool) (N : Nat) (s : State) (hN : N ≤ 8) :
    WP isa (.block (if ctr then [] else [.subi .r6 .r6 (16 * (batchRegs N).length)])) s fun t =>
      t.gpr .r6 = (if ctr then s.gpr .r6 else s.gpr .r6 - BitVec.ofNat 64 (16*N)) ∧
      Local [.r6] [] s t := by
  cases ctr <;> apply WP.of_runBlock
  · simp only [Bool.false_eq_true, ite_false, batchRegs, List.length_map, List.length_range,
      runBlock_cons, runStep_some, reduceExec, ne_eq, reduceCtorEq, not_false_eq_true, show 16*N ≤ 2^15 by omega,
      and_self, ite_true,
      runBlock_nil, Option.some.injEq, exists_eq_left']
    exact ⟨by simp only [RegUpd.gpr_write_self], Local.write s .r6 _⟩
  · simp only [ite_true, runBlock_nil, Option.some.injEq, exists_eq_left']
    exact ⟨True.intro, Local.refl _ _ _⟩

structure BatchRead (ctr : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  effects : Local [.r6, .r8] (counterWord :: batchRegs N) s₀ s
  ptr : s.gpr .r6 = s₀.gpr .r6
  counter : s.gpr .r8 = if ctr then s₀.gpr .r8 + BitVec.ofNat 64 N else s₀.gpr .r8
  val : ∀ i < N, s.vpr (breg i) = readValue ctr s₀ i

theorem batch_read_ok (ctr : Bool) (N : Nat) (s : State) (hN : N ≤ 8)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hc : ctr = true → s.vpr counterMask = counterControl)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((batchRegs N).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock ctr) ++
      (if ctr then [] else [.subi .r6 .r6 (16 * (batchRegs N).length)]))) s (BatchRead ctr s N) := by
  rw [WP.block_append_iff]
  refine WP.mono (read_ok ctr hN s h0 hm hc hr) fun t ht => ?_
  refine WP.mono (rewind_ok ctr N t hN) fun u ⟨hu, he⟩ => ?_
  refine ⟨(ht.effects.trans he).weaken (by simp) (by simp), ?_, ?_, ?_⟩
  · rw [hu, ht.ptr]
    cases ctr <;> simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.add_sub_cancel]
  · rw [he.keep.gpr (by decide), ht.counter]
  · intro i hi
    rw [he.v _ (by simp), ht.val i hi]

structure BatchCipher (inverse ctr : Bool) (s₀ : State) (nr N : Nat) (s : State) : Prop where
  effects : Local [.r6, .r8, .r9, .r10] (key :: counterWord :: batchRegs N) s₀ s
  ptr : s.gpr .r6 = s₀.gpr .r6
  counter : s.gpr .r8 = if ctr then s₀.gpr .r8 + BitVec.ofNat 64 N else s₀.gpr .r8
  val : ∀ i < N, aesState (s.vpr (breg i)) =
    result inverse nr (schedule nr s₀) (aesState (readValue ctr s₀ i))

theorem batch_cipher_ok (inverse ctr : Bool) (N : Nat) (s : State) {nr : Nat} (hN : N ≤ 8)
    (hp : Inputs nr s) (hc : ctr = true → s.vpr counterMask = counterControl)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.seq (.block ((batchRegs N).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock ctr) ++
      (if ctr then [] else [.subi .r6 .r6 (16 * (batchRegs N).length)])))
      (Impl.Aes.PPC64LE.Crypto.aes inverse (batchRegs N))) s (BatchCipher inverse ctr s nr N) := by
  have facts := batchFacts ⟨N, by omega⟩
  refine WP.seq (WP.mono (batch_read_ok ctr N s hN hp.zero hp.mask hc hr) fun t ht => ?_)
  have hpt : Inputs nr t := by
    refine ⟨(ht.effects.keep.gpr (by decide)).trans hp.zero,
      (ht.effects.v mask (by simp [facts.2.2.1, mask, counterWord])).trans hp.mask,
      (ht.effects.keep.gpr (by decide)).trans hp.rounds, hp.min, hp.max, ?_⟩
    intro j hj
    rw [ht.effects.keep.2.1, ht.effects.keep.2.2, ht.effects.keep.gpr (by decide)]
    exact hp.reads j hj
  refine WP.mono (aes_ok inverse (batchRegs N) facts.1 facts.2.1 facts.2.2.1 hpt) fun u ⟨hv, he⟩ => ?_
  refine ⟨(ht.effects.trans he).weaken (by simp) (by simp [or_left_comm]), ?_, ?_, ?_⟩
  · exact (he.keep.gpr (by decide)).trans ht.ptr
  · exact (he.keep.gpr (by decide)).trans ht.counter
  · intro j hj
    rw [hv _ (breg_mem hj), ht.val j hj]
    have hs : schedule nr t = schedule nr s := by
      rw [schedule, ht.effects.mem, ht.effects.keep.gpr (by decide)]
    rw [hs]

theorem count_ok (N : Nat) (s : State) (hN : N ≤ 8) :
    WP isa (.block [.subi .r7 .r7 N]) s fun t =>
      t.gpr .r7 = s.gpr .r7 - BitVec.ofNat 64 N ∧ Local [.r7] [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, reduceExec, ne_eq, reduceCtorEq, not_false_eq_true,
    show N ≤ 2^15 by omega, and_self, ite_true, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., Local.write s .r7 _⟩

structure BatchDone (ctr : Bool) (s₀ : State) (m₀ : Mem) (D : Addr) (n k N : Nat)
    (F : Nat → Spec.Aes.State) (s : State) : Prop where
  keep : Keep [.r6, .r7, .r8, .r9, .r10] s₀ s
  ptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*(k+N))
  counter : s.gpr .r8 = if ctr then s₀.gpr .r8 + BitVec.ofNat 64 N else s₀.gpr .r8
  left : s.gpr .r7 = s₀.gpr .r7 - BitVec.ofNat 64 N
  processed : Processed m₀ s.mem D n (k+N) F
  frame : Frame [⟨D, 16*n⟩] s₀.mem s.mem
  fixed : ∀ r, r ∉ key :: data :: counterWord :: batchRegs N → s.vpr r = s₀.vpr r

theorem group_ok (inverse ctr : Bool) (N : Nat) (s : State) {nr n k : Nat} {m₀ : Mem}
    {D : Addr} {F : Nat → Spec.Aes.State} (hN : N ≤ 8) (hkn : k+N ≤ n) (hsize : 16*n ≤ 2^64)
    (hp : Inputs nr s) (hc : ctr = true → s.vpr counterMask = counterControl)
    (hw : (⟨D, 16*n⟩ : Region) ∈ s.wr)
    (hptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*k)) (hproc : Processed m₀ s.mem D n k F)
    (hF : ∀ i < N, ∀ v, aesState v = result inverse nr (schedule nr s) (aesState (readValue ctr s i)) →
      ∀ m, Processed m₀ m D n (k+i) F →
        aesState (outputAt ctr v m (D + BitVec.ofNat 64 (16*(k+i)))) = F (k+i)) :
    WP isa (Impl.Aes.PPC64LE.Crypto.group inverse ctr N) s (BatchDone ctr s m₀ D n k N F) := by
  have hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (16*i)) 16 := by
    intro i hi
    rw [hptr, Offset.add_add]
    exact ⟨⟨D, 16*n⟩, List.mem_append_right _ hw,
      Offset.contains_base D (d := 16*k+16*i) (n := 16) (k := 16*n) (by omega) (by omega)⟩
  have hb := batch_cipher_ok inverse ctr N s hN hp hc hr
  rw [Impl.Aes.PPC64LE.Crypto.group]
  refine WP.seq (WP.mono (WP.seq_iff.mp hb) fun t ht => ?_)
  refine WP.seq (WP.mono ht fun u hu => ?_)
  rw [WP.block_append_iff]
  have hzero : u.gpr .r0 = 0 := (hu.effects.keep.gpr (by decide)).trans hp.zero
  have hmask : u.vpr mask = byteMask := by
    have facts := batchFacts ⟨N, by omega⟩
    exact (hu.effects.v mask (by simp [facts.2.2.1, mask, key, counterWord])).trans hp.mask
  have hwu : (⟨D, 16*n⟩ : Region) ∈ u.wr := by rw [hu.effects.keep.2.2]; exact hw
  have hpu : u.gpr .r6 = D + BitVec.ofNat 64 (16*k) := hu.ptr.trans hptr
  have hpr : Processed m₀ u.mem D n k F := by rw [hu.effects.mem]; exact hproc
  refine WP.mono (write_ok ctr hN hkn hsize hwu hzero hmask hpu hpr
    (fun i hi m hm => hF i hi _ (hu.val i hi) m hm)) fun v hv => ?_
  simp only [batchRegs, List.length_map, List.length_range]
  refine WP.mono (count_ok N v hN) fun w ⟨hl, he⟩ => ?_
  refine ⟨((hu.effects.keep.trans hv.keep).trans he.keep).mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (he.keep.gpr (by decide)).trans hv.ptr
  · rw [he.keep.gpr (by decide), hv.keep.gpr (by decide), hu.counter]
  · rw [hl, hv.keep.gpr (by decide), hu.effects.keep.gpr (by decide)]
  · rw [he.mem]; exact hv.processed
  · rw [he.mem, ← hu.effects.mem]; exact hv.frame
  · intro r hr
    have hr' : r ≠ key ∧ r ≠ data ∧ r ≠ counterWord ∧ r ∉ batchRegs N := by
      simpa only [List.mem_cons, not_or] using hr
    rw [he.v r (by simp), hv.fixed r (by simp [hr'.2.1, hr'.2.2.2]),
      hu.effects.v r (by simp [hr'.1, hr'.2.2.1, hr'.2.2.2])]

end VG.Proof.Aes.PPC64LE.Crypto
