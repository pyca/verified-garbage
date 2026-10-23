module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Kernel
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # The complete 18- or 24-round serial kernel and output whitening -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Camellia.AArch64.Serial

theorem body_wp {s : State} {R : Nat} (hR : R = 18 ∨ R = 24)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 R) (hc : Context s)
    (hw0 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 768) 8)
    (hw1 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 776) 8)
    (m : BitVec 128)
    (initial : halves s = ((m >>> 64).setWidth 64 ^^^ keyWord s 0,m.setWidth 64 ^^^ keyWord s 1)) :
    WP isa cryptBody s fun t =>
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (s.gpr .x5+BitVec.ofNat 64 768) 16 =
        (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (R/6) (keyWord s) m)).toList ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have finish (u : State) (uc : Context u) (us : Stable s u)
      (hu : halves u = VG.Proof.Camellia.groups (R/6) (keyWord s) (halves s)) :
      WP isa (.block (whitening (8*(R/6)))) u fun t =>
        (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
        Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
        Spec.Aes.bytesAt t.mem (s.gpr .x5+BitVec.ofNat 64 768) 16 =
          (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (R/6) (keyWord s) m)).toList ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
    obtain ⟨t,te,to,tg,tf,trd,twr,_⟩ := whitening_run u (8*(R/6))
      (by rcases hR with rfl | rfl <;> decide) uc.read
      (by rw [us.wr,us.regs .x5 (by decide)]; exact hw0)
      (by rw [us.wr,us.regs .x5 (by decide)]; exact hw1)
    refine WP.of_runBlock ⟨t,te,fun r hr => (tg r hr).trans (us.regs r hr),?_,?_,
      trd.trans us.rd,twr.trans us.wr⟩
    · simpa only [us.mem,us.regs .x5 (by decide)] using tf
    · change Spec.Aes.bytesAt t.mem (u.gpr .x5+BitVec.ofNat 64 768) 16 =
        (Spec.Camellia.encodeBlock (((halves u).2 ^^^ keyWord u (8*(R/6))) ++
          ((halves u).1 ^^^ keyWord u (8*(R/6)+1)))).toList at to
      rw [us.regs .x5 (by decide),hu,us.keys,initial] at to
      exact to
  change WP isa (.seq (.block (roundsPrefix ++ [.subImm .x .x8 .x1 18])) _) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain ⟨a,ae,ac,as,av⟩ := partial_run hc
  refine WP.of_runBlock ⟨a,ae,?_⟩
  let z := a.write .x .x8 (a.read .x .x1 - BitVec.ofNat 64 18)
  have az : Stable a z := by
    refine ⟨fun r hr => gpr_write_of_ne _ _ _ ?_,rfl,rfl,rfl,rfl⟩
    exact fun h => hr (h ▸ (by decide : Reg.x8 ∈ written))
  have sz := as.trans az
  have zc : Context z := by
    refine ⟨ac.constants,?_,ac.table,ac.read_stable az⟩
    refine ⟨ac.masks.1,?_,?_⟩
    · rw [az.regs .x13 (by decide)]; exact ac.masks.2.1
    · rw [az.regs .x14 (by decide)]; exact ac.masks.2.2
  have zh : halves z = partialRounds (keyWord s) (halves s) := by
    rw [halves,show z.gpr .x6 = a.gpr .x6 from gpr_write_of_ne _ _ _ (by decide),
      show z.gpr .x7 = a.gpr .x7 from gpr_write_of_ne _ _ _ (by decide)]
    exact av
  refine WP.of_runBlock ⟨z,by
    rw [runBlock_cons,exec_subImm_x (by decide),runStep_some,runBlock_nil],?_⟩
  refine WP.ite (decide (R=18)) ?_ (fun h => ?_) (fun h => ?_)
  · have v : z.gpr .x8 = BitVec.ofNat 64 R - BitVec.ofNat 64 18 := by
      simp only [z,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
        as.regs .x1 (by decide),hx1]
    change some (z.read .x .x8 == 0) = _
    simp only [State.read,Size.bits,BitVec.setWidth_eq,v]
    rcases hR with rfl | rfl <;> decide
  · have he : R = 18 := of_decide_eq_true h
    subst R
    exact finish z zc sz (by rw [zh,partialRounds_eq])
  · have he : R = 24 := by
      have hn : R ≠ 18 := of_decide_eq_false h
      rcases hR with hR | hR
      · exact False.elim (hn hR)
      · exact hR
    subst R
    rw [WP.block_append_iff]
    obtain ⟨b,be,bc,bs,bv⟩ := last_run zc
    refine WP.of_runBlock ⟨b,be,?_⟩
    exact finish b bc (sz.trans bs) (by rw [bv,zh,sz.keys,lastRounds_eq])

end VG.Proof.Camellia.AArch64.Serial
