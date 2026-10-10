import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue

/-! ## From `BoundedFourMaskLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem maskGuard {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) :
    isa.eval (.nonzero .x .x5) s=some (decide (j<64)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega

theorem maskLoop_ok {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) (hj : j<64)
    (hr : ∀i<64,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5)) s
      (fun t=>MaskInv σ t p v 64) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=64-j ∧MaskInv σ s p v j ∧j<64)
    ?_ (64-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (maskStep_ok hi hj hr hw) fun t ht=>?_
  have hg:=maskGuard ht
  by_cases hn : j+1<64
  · exact .inr ⟨by rw [hg,decide_eq_true hn],64-(j+1),by omega,j+1,rfl,ht,hn⟩
  · have he : j+1=64 := by omega
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def outputMask (x : BitVec 64) : BitVec 128 := if x=0#64 then ~~~0#128 else 0#128

def maskScalar : List Instr :=
 [.subImm .x .x4 .x4 1,.lsr .x .x4 .x4 63,.movz .x .x6 0 0,.sub .w .x4 .x6 .x4]

theorem maskScalar_ok (s : State) (hx : (s.gpr .x4).toNat≤256) :
    WP isa (.block maskScalar) s fun t=>
      ((t.gpr .x4=(if s.gpr .x4=0#64 then 4294967295#64 else 0#64) ∧t.mem=s.mem) ∧
        Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskScalar
  arun
  have h:=ResidentRej.smallFlag_status (s.gpr .x4) (by omega)
  rw [h]
  by_cases hz : s.gpr .x4=0#64
  · simp only [ite_eq_left hz]
    rfl
  · simp only [ite_eq_right hz]
    rfl

def maskFooter (k : Nat) : List Instr :=
 [.addImm .x .x3 .x21 (1024*k),.movz .x .x5 64 0]

theorem maskFooter_ok (s : State) {k : Nat} (hk : k<4) :
    WP isa (.block (maskFooter k)) s fun t=>
      ((t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧t.mem=s.mem) ∧
        Keep [.x3,.x5] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskFooter
  have hb : 1024*k<4096 := by omega
  arun [hb]


def maskLoadScalar (k : Nat) : List Instr := .ldr .x .x4 .x19 (7904+8*k)::maskScalar

theorem maskLoadScalar_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskLoadScalar k)) s fun t=>
      ((t.gpr .x4=(if s.mem.readW (countAt b k) 64=0#64 then 4294967295#64 else 0#64) ∧
        t.mem=s.mem) ∧Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold maskLoadScalar
  refine wp_ldrx (by omega) (by rw [hb]; rfl) hr fun a ha h4=>?_
  refine WP.mono (maskScalar_ok a (by rw [h4]; exact hx)) fun t ⟨⟨⟨hv,hm⟩,ht⟩,_⟩=>?_
  exact ⟨⟨by rw [hv,h4],hm.trans ha.mem⟩,(ha.keep.trans ht).mono (by decide)⟩

def maskSetup (k : Nat) : List Instr := maskLoadScalar k ++
 [.vop (.dup .s4 .v0 .x4)]++maskFooter k

theorem maskSetup_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskSetup k)) s fun t=>
      InitKeep [.x3,.x4,.x5,.x6] [.v0] s t ∧
      t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧
      t.v .v0=outputMask (s.mem.readW (countAt b k) 64) := by
  unfold maskSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (maskLoadScalar_ok hk hb hr hx) fun a ⟨⟨⟨h4,hm⟩,ha⟩,hv⟩=>?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v0) rfl fun c hc=>?_
  refine WP.mono (maskFooter_ok c hk) fun t ⟨⟨⟨hp,h5,htm⟩,ht⟩,htv⟩=>?_
  refine ⟨?_,?_,h5,?_⟩
  · refine ⟨((ha.trans (hc.keep (by decide))).trans ht).mono (by decide),?_,?_⟩
    · rw [htm,hc.mem,hm]
    · intro r hr
      rw [htv,hc.other r (by simpa using hr),hv]
  · rw [hp,hc.gpr,ha.get .x21]
  · rw [htv,hc.v,h4]
    unfold outputMask
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
