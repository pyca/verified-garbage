module

public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Proof.AesCbc.X86.Body
public import VerifiedGarbage.Proof.Aes.X86.Chain
import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-CBC, AES-CFB128 and AES-OFB on x86, around a chain

A mode's code around any implementation of AES for a chain of blocks
(`Impl.AesCbc.X86.wholeChain`) meets the mode's contract (`modeX86`), and
leaves the scratch buffer but the chain's bytes unchanged, or zero where it
saved the registers (`zeroedAt`; `chain_wp`), if one block's step is the mode's
(`StepOk`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Chain

open VG VG.X86
open VG.Impl.Aes.X86 (Chain)
open VG.Impl.AesCbc.X86 (wholeChain)
open VG.Proof.Aes.X86 (reg32)
open VG.Proof.Aes.X86.AesNi (st st_ext getD_ofFn getD_st byte_xor)
open VG.Proof.Aes.X86.Chain (ChainOk ModeOk Env Out Keyed changed changed_cases upd pxor mid_wp st_readW st_getD)
open VG.Spec.Aes (bytesAt)

/-- `pxor` of two registers is `⊕` of their bytes. -/
theorem st_xor (d o : BitVec 128) : (st (pxor d o)).toList = Spec.Cbc.xor (st d).toList (st o).toList := by
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [st_getD _ hi, xor_eq, Proof.Cmac.getD_xor (by simp) (by simpa using hi), st_getD d hi, st_getD o hi]
  exact byte_xor d o i

theorem pxor_comm (a b : BitVec 128) : pxor a b = pxor b a := BitVec.xor_comm _ _

/-- The same, the operands the other way round. -/
theorem st_xor' (o d : BitVec 128) :
    (st (XBinOp.eval .pxor o d)).toList = Spec.Cbc.xor (st d).toList (st o).toList :=
  (congrArg (fun v => (st v).toList) (pxor_comm o d)).trans (st_xor d o)

/-- The cipher of a register, as the modes apply it to a block's bytes. -/
theorem aesWith_st (R : Nat) (w : List Byte) {x e : BitVec 128} (h : st e = Spec.Aes.cipher R w (st x)) :
    (st e).toList = Spec.Cbc.aesWith R w (st x).toList := by
  rw [h]
  exact congrArg (fun y => (Spec.Aes.cipher R w y).toList) (st_ext fun i hi => by
    rw [getD_ofFn hi]
    exact (st_getD _ hi).trans (getD_st _ hi).symm).symm

/-- One block's step is `M`'s: from the chaining value `x` after `k` blocks,
the block `d` and the cipher `e` of what the step enciphers, the block and the
next chaining value. -/
def StepOk (M : Mode) (f g w : BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  ∀ {s₀ : State} {k : Nat} (hk : k < N s₀) {x d e : BitVec 128}, (st x).toList = chainK M s₀ k →
    (st d).toList = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) →
    (st e).toList = Spec.Cbc.aesWith (R s₀) (wK s₀) (st (f x d)).toList →
    outK M s₀ (k + 1) = outK M s₀ k ++ [(st (w e d)).toList] ∧ (st (g e d)).toList = chainK M s₀ (k + 1)

section
variable {c : Chain} {m : Chain.Mode} {M : Mode} {f g w : BitVec 128 → BitVec 128 → BitVec 128} {s₀ : State}

theorem env_of (hp : UPre s₀) {s : State} (h : LInv M s₀ 0 s) :
    Env (W s₀) (R s₀) (Iv s₀) (Dp s₀) (N s₀) (S s₀) s ∧ Out (W s₀) (Dp s₀) (N s₀) s := by
  have big := UPre.big_of h.frame
  have ha : ∀ i, argAddr s i = argAddr s₀ i := fun i => by simp only [argAddr, h.esp]
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have arg' : ∀ {i : Nat}, i < 6 → arg s i = arg s₀ i := fun hi => by
    show s.mem.readW (argAddr s _) 32 = _
    rw [ha]; exact hp.arg_keep big hi
  refine ⟨{ a0 := arg' (by decide), a1 := by rw [arg' (by decide)]; exact (BitVec.ofNat_toNat ..).symm ▸ (BitVec.setWidth_eq _).symm
            a2 := arg' (by decide), a3 := arg' (by decide)
            a4 := by rw [arg' (by decide)]; exact (BitVec.ofNat_toNat ..).symm ▸ (BitVec.setWidth_eq _).symm
            a5 := arg' (by decide)
            argIn := fun i hi => by rw [hrw, ha]; exact hp.arg_in hi
            argScr := fun i hi => by rw [ha]; exact hp.args_scr.sub_left (hp.arg_sub hi)
            rounds := hp.rounds, schFit := hp.sch_fit, sch := by rw [hrw, hp.rd]; simp
            schScr := hp.sch_scr, scrFit := hp.scr_fit, scr := by rw [h.wr, hp.wr]; simp
            iv := by rw [h.wr, hp.wr]; simp
            ivScr := hp.iv_scr, datFit := hp.data_fit, dat := by rw [hrw, hp.wr]; simp
            datScr := hp.data_scr },
    { wr := by rw [h.wr, hp.wr]; simp
      sch := hp.sch_data
      args := fun i hi => by rw [ha]; exact hp.args_data.sub_left (hp.arg_sub hi) }⟩

/-- The chain, from the prologue to the epilogue. -/
theorem chain_mid (hc : ChainOk c) (hm : ModeOk m f g (some w)) (hM : StepOk M f g w) (hp : UPre s₀) {s : State}
    (h : LInv M s₀ 0 s) (hn : 0 < N s₀) :
    WP isa (c.mid m) s fun t => LInv M s₀ (N s₀) t ∧ Frame (FB s₀ c.written) s.mem t.mem := by
  obtain ⟨he, ho⟩ := env_of hp h
  have hle := hc.le
  have hs := UPre.sched_bytes hp (UPre.big_of h.frame)
  have hdf := hp.data_fit
  have wsub : Region.Sub (reg32 (S s₀) c.written) (scrR s₀) := Region.sub_prefix (by omega_using [hle])
  have keep : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, (dataR s₀).Disjoint r) →
      Spec.Cbc.blocksAt m' ((Dp s₀).setWidth 64) (N s₀) = Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) :=
    fun hf hd => List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf
      (fun r hr => (hd r hr).sub_left (UPre.data_sub (List.mem_range.mp hj))) (by decide)
  refine WP.mono (mid_wp (w := some w) hc hm he (fun _ => ho) hn (I := fun k x m' =>
    Spec.Cbc.blocksAt m' ((Dp s₀).setWidth 64) (N s₀) = outK M s₀ k ++ (blks s₀).drop k ∧
      (st x).toList = chainK M s₀ k) ⟨h.data, by rw [st_readW]; exact h.iv⟩ (fun hI hf => ?_) (fun hk hI hE => ?_))
    fun t ⟨x, m', hI, hf, hm', esi, esp, rd, wr⟩ => ?_
  · refine ⟨(keep hf fun r hr => ?_).trans hI.1, hI.2⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_scr.sub_right wsub
  · obtain ⟨hd, hx⟩ := hI
    rename_i k x e mk
    obtain ⟨o1, o2⟩ := hM (s₀ := s₀) hk hx ((st_readW _ _).trans (block_of_data hd hk))
      (by rw [aesWith_st _ _ hE]; exact congrArg (fun l => Spec.Cbc.aesWith (R s₀) l _) hs)
    refine ⟨?_, o2⟩
    have hl : (outK M s₀ k).length = k := by rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
    have fw : Frame [⟨blk s₀ k, 16⟩] mk (mk.writeW (blk s₀ k) (w e (mk.readW (blk s₀ k) 128))) :=
      (Frame.refl _ _).writeW (r := ⟨blk s₀ k, 16⟩) List.mem_cons_self _ (Region.contains_self _ _)
    show Spec.Cbc.blocksAt (mk.writeW (blk s₀ k) (w e (mk.readW (blk s₀ k) 128))) _ _ = _
    rw [hp.blocksAt_step hk (fw.mono (by simp)), hd, o1, ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide),
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · have fiv : Frame [ivR s₀] m' t.mem := by
      rw [hm']
      exact (Frame.refl _ _).writeW (r := ivR s₀) List.mem_cons_self _ (Region.contains_self _ _)
    have all : Frame [ivR s₀, dataR s₀, reg32 (S s₀) c.written] s.mem t.mem :=
      (hf.mono fun r hr => by rcases changed_cases hr with rfl | ⟨-, rfl⟩ <;> simp).trans (fiv.mono (by simp))
    refine ⟨⟨esi, esp.trans h.esp, rd.trans h.rd, wr.trans h.wr, h.frame.trans (all.sub fun r hr => ?_), ?_, ?_⟩,
      all.mono fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by omega_using [hle])⟩
    · refine (keep fiv fun r hr => ?_).trans hI.1
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm
    · rw [hm', ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      exact hI.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp

/-- The whole function: the mode's contract, and the scratch buffer but the
chain's bytes zero at the offsets `zeroedAt` and unchanged at the others. -/
theorem chain_wp (hc : ChainOk c) (hm : ModeOk m f g (some w)) (hM : StepOk M f g w) (h0 : (modeX86 M).pre s₀) :
    WP isa (wholeChain c m) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' ∧
      ∀ i, c.written ≤ i → i < 2176 →
        s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) =
          if zeroedAt i then 0 else s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) :=
  endsZ_wp h0 fun h hn => chain_mid hc hm hM (UPre.of h0) h hn

end

end VG.Proof.AesCbc.X86.Chain
