module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm4.Arm.Batch32Loop
public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Fill
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Functional composition of the prepared, eight-block SM4 counter mode with `inc₃₂`

As `BatchBody`, and the blocks and the counter block it leaves as
`Spec.Gcm.ctr32`'s and `inc₃₂ⁿ` of the counter block (`ctr32_of_blocks`,
`next32_eq`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Body

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr)
open VG.Proof.Sm4.Arm.BatchFill (bytes_frame)
open VG.Proof.Sm4.Arm.BatchEntry (mode_slots restore_wp)
open VG.Proof.Sm4.Arm.BatchChain (ChainPre counterOut_wp)
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions)
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Proof.Sm4.Arm.Batch32Fill (next32 next32_eq)
open VG.Proof.Sm4.Arm.Batch32Loop (loopOrEmpty_wp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

theorem cipher_length (K : Spec.Sm4.Schedule) (b : List Byte) : (Spec.Sm4.cipher K b).length = 16 :=
  Vector.length_toList

attribute [local irreducible] Spec.Sm4.cipher

/-- The blocks of counter mode with `inc₃₂` from the counter block `t`, one
at a time, as `Spec.Gcm.ctr32`'s. -/
theorem ctr32_of_blocks {K : Spec.Sm4.Schedule} {m₀ m : Mem} {D : Addr} {n : Nat} {t : List Byte}
    (ht : t.length = 16)
    (h : ∀ j < n, bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16) (Spec.Sm4.cipher K (next32 t j))) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher K) (Spec.Gcm.ofBytes t) (Spec.Gcm.blocksAt m₀ D n) := by
  have hl : (Spec.Gcm.blocksAt m₀ D n).length = n := by simp [Spec.Gcm.blocksAt]
  rw [Spec.Gcm.ctr32, hl, Spec.Gcm.keystream, Spec.Gcm.blocksAt, Spec.Gcm.blocksAt, List.zipWith_map,
    List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hctr : Spec.Gcm.toBytes (Nat.repeat Spec.Gcm.inc32 j (Spec.Gcm.ofBytes t)) = next32 t j := by
    rw [Proof.Modes.toBytes_eq_ofNat, Proof.Modes.toNat_repeat_inc32, Proof.Modes.toNat_ofBytes ht,
      next32_eq ht]
  rw [Spec.Sm4.gcmCipher, hctr, Spec.Gcm.blockAt, Spec.Gcm.blockAt, h j hj]
  exact Ocb.ofBytes_xor (Cmac.bytesAt_length _ _ _) (cipher_length _ _)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Gcm.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (Spec.Gcm.blockAt s₀.mem (State.addr (Iv s₀))) (Spec.Gcm.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : Spec.Gcm.blockAt s.mem (State.addr (Iv s₀)) =
    Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.blockAt s₀.mem (State.addr (Iv s₀)))
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCtr32.ctr32 s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  have hl : (bytesAt s₀.mem (State.addr (Iv s₀)) 16).length = 16 := Cmac.bytesAt_length _ _ _
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have plain₁ : ∀ j < N s₀, bytesAt s₁.mem (dataAddr (Dp s₀) j) 16 = bytesAt s₀.mem (dataAddr (Dp s₀) j) 16 :=
    fun j hj => bytes_frame p.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ds.sub_left (Offset.sub_base _ (by change 16 * j + 16 ≤ 16 * N s₀; omega))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have out₃ : ∀ j < N s₀, bytesAt s₃.mem (dataAddr (Dp s₀) j) 16 =
      Spec.Cbc.xor (bytesAt s₀.mem (dataAddr (Dp s₀) j) 16)
        (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀)))
          (next32 (bytesAt s₀.mem (State.addr (Iv s₀)) 16) j)) := by
    intro j hj
    rw [bytes_frame c.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.id.symm.sub_left (Offset.sub_base _ (by change 16 * j + 16 ≤ 16 * N s₀; omega))),
      l.blocks j hj, Batch32Loop.outBlock, plain₁ j hj]
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, Spec.Gcm.blockAt]
    exact ctr32_of_blocks hl out₃
  · rw [mem]
    refine Proof.Modes.ctr32_next ?_
    rw [c.block, l.counter, next32_eq hl]

end VG.Proof.Sm4.Arm.Batch32Body
