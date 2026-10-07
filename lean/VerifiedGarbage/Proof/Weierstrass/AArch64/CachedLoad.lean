import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- The cached powers share the odd-table index without destroying it. -/
theorem cachedAddress_ok {s : State} {base : Addr} {a : Nat}
    (h0 : s.gpr .x0=base) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) :
    WP isa (.block [.subImm .x .x17 .x2 1,.lsl .x .x17 .x17 6,
      .movz .x .x16 6000 0,.add .x .x16 .x0 .x16,.add .x .x16 .x16 .x17]) s fun t =>
      t.gpr .x16=off base (6000+64*(a-1)) ∧ Keeps [.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,h0,h2,show 1<4096 by decide,show 6<64 by decide,
    show 16*0<64 by decide,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
    have sh : BitVec.ofNat 64 (a-1) <<< 6=BitVec.ofNat 64 (64*(a-1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
      rw [Nat.mul_mod,Nat.mod_mod,←Nat.mul_mod]
      congr 1
      omega
    rw [sh]
    simp only [show (6000 : BitVec 16).setWidth 64=BitVec.ofNat 64 6000 by decide,off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- Load both cached powers into the addition inputs. -/
theorem cachedLoad_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha8 : a≤8) (hsize : 6512≤size) :
    WP isa (.block CachedJac.load) s fun t =>
      wordsVal t.mem base 5400 4=wordsVal s.mem base (6000+64*(a-1)) 4 ∧
      wordsVal t.mem base 5432 4=wordsVal s.mem base (6032+64*(a-1)) 4 ∧
      KeepRegs [.x4,.x16,.x17] s t ∧ Outside base 5400 64 s.mem t.mem := by
  rw [CachedJac.load,WP.block_append_iff]
  refine WP.mono (cachedAddress_ok hs.x0 h2 ha) fun b ⟨b16,kb⟩ => ?_
  refine WP.mono (jacWords_ok (n:=8) (hs.of_keeps kb (by decide)) b16
    (by omega) (by decide) (by omega) (by omega) 8 (by decide)) fun t ⟨hv,kt,ot⟩ => ?_
  refine ⟨?_,?_,((Keeps.regs kb).mono (by sub_regs)).trans (kt.mono (by sub_regs)),?_⟩
  · refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [kb.mem] using hv i (by omega)
  · refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    have e := hv (4+i) (by omega)
    rw [show 5400+8*(4+i)=5432+8*i by omega,
      show 6000+64*(a-1)+8*(4+i)=6032+64*(a-1)+8*i by omega,kb.mem] at e
    exact e
  · simpa only [kb.mem] using ot

/-- The selected canonical powers become initialized field slots. -/
theorem cachedLoadField_ok {M : Mod} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n=4)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv M base size C.p Sl V E s)
    (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) (ha8 : a≤8) (hsize : 6512≤size)
    (hD : ∀ x∈[5400,5432],Sl x)
    (hT : ∀ x∈[6000+64*(a-1),6032+64*(a-1)],x∈V) :
    WP isa (.block CachedJac.load) s fun t =>
      ProgKeep M base [5400,5432] s t ∧
      Inv M base size C.p Sl ([5400,5432]++V) (tmv C M.n base t) t ∧
      tmv C M.n base t 5400=E (6000+64*(a-1)) ∧
      tmv C M.n base t 5432=E (6032+64*(a-1)) ∧ t.gpr .x2=s.gpr .x2 := by
  refine WP.mono (cachedLoad_ok hI.scr h2 ha ha8 hsize) fun t ⟨v2,v3,kt,ot⟩ => ?_
  have kp : ProgKeep M base [5400,5432] s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,kt.sp,fun x hx _ => ot x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [clob]
    · have h0 := hx 5400 (by simp)
      have h1 := hx 5432 (by simp)
      rw [hn] at h0 h1
      omega
  refine ⟨kp,hI.of_progKeep hL kp hD ?_,?_,?_,kt.gpr _ (by decide)⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · rw [hn,v2]; simpa only [hn] using hI.lt _ (hT _ (by simp))
    · rw [hn,v3]; simpa only [hn] using hI.lt _ (hT _ (by simp))
  · unfold tmv
    rw [hn,v2]
    simpa only [hn] using hI.val _ (hT _ (by simp))
  · unfold tmv
    rw [hn,v3]
    simpa only [hn] using hI.val _ (hT _ (by simp))

end VG.Proof.Weierstrass.AArch64
