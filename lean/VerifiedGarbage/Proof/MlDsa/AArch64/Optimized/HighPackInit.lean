import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Proof.MlKem.AArch64 (wp_scalar wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep pairConst_ok)

def repeatedWord (n : Nat) : BitVec 128 :=
  ofVWords (BitVec.ofNat 32 n) (BitVec.ofNat 32 n) (BitVec.ofNat 32 n) (BitVec.ofNat 32 n)

/-- The short scalar materialization initializes all four lanes, preserving
memory and every other vector register. -/
theorem vc_ok (s : State) (d : VReg) (n : Nat) :
    WP isa (.block (vc d n)) s fun t => ConstKeep d s t ∧ t.v d=repeatedWord n := by
  unfold vc
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x9 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d := d) rfl fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hk.gpr r (by simpa using hr)]
    · rw [ht.other r hr,hv]
    · rw [ht.mem,hm]
    · rw [ht.rd,hk.rd]
    · rw [ht.wr,hk.wr]
    · rw [ht.sp,hk.sp]
  · rw [ht.v,ha]
    change ofVWords _ _ _ _ = repeatedWord n
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq, repeatedWord]

theorem repeatedWord_lane (n : Nat) {e : Nat} (he : e<4) :
    vword (repeatedWord n) e=BitVec.ofNat 32 n := by
  unfold repeatedWord
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

structure SetupKeep (rs : List VReg) (s t : State) : Prop where
  gpr : ∀ r, r≠.x9 → t.gpr r=s.gpr r
  vec : ∀ r, r∉rs → t.v r=s.v r
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

theorem SetupKeep.ofConst {d : VReg} {s t : State} (h : ConstKeep d s t) :
    SetupKeep [d] s t :=
  ⟨h.gpr,fun r hr => h.vec r (by simpa using hr),h.mem,h.rd,h.wr,h.sp⟩

theorem SetupKeep.trans {rs qs : List VReg} {s t u : State}
    (h : SetupKeep rs s t) (k : SetupKeep qs t u) : SetupKeep (rs++qs) s u := by
  refine ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr),?_,
    k.mem.trans h.mem,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
  intro r hr
  rw [List.mem_append,not_or] at hr
  exact (k.vec r hr.2).trans (h.vec r hr.1)

/-- Initialize the three shuffle tables and zero vector used by both packers. -/
theorem packSetup_ok (s : State) :
    WP isa (.block packSetup) s fun t =>
      SetupKeep [.v28,.v29,.v24,.v25] s t ∧
      t.v .v28=0 ∧
      t.v .v29=ofVDwords 0x0908060504020100 0xffffffff0e0d0c0a ∧
      t.v .v24=ofVDwords 0xffff0504ffff0100 0xffff0d0cffff0908 ∧
      t.v .v25=ofVDwords 0xffff0706ffff0302 0xffff0f0effff0b0a := by
  change WP isa (.block (.vop (.movi0 .v28) ::
    ((Impl.MlKem.AArch64.movImm .x9 0x0908060504020100 ++ [.vop (.dup .d2 .v29 .x9)] ++
      Impl.MlKem.AArch64.movImm .x9 0xffffffff0e0d0c0a ++ [.vop (.ins .d2 .v29 1 .x9)]) ++
    (Impl.MlKem.AArch64.movImm .x9 0xffff0504ffff0100 ++ [.vop (.dup .d2 .v24 .x9)] ++
      Impl.MlKem.AArch64.movImm .x9 0xffff0d0cffff0908 ++ [.vop (.ins .d2 .v24 1 .x9)]) ++
    (Impl.MlKem.AArch64.movImm .x9 0xffff0706ffff0302 ++ [.vop (.dup .d2 .v25 .x9)] ++
      Impl.MlKem.AArch64.movImm .x9 0xffff0f0effff0b0a ++ [.vop (.ins .d2 .v25 1 .x9)])))) s _
  refine wp_vop (d := .v28) rfl fun a ha => ?_
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (pairConst_ok a .v29 _ _) fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairConst_ok b .v24 _ _) fun c hc => ?_
  refine WP.mono (pairConst_ok c .v25 _ _) fun t ht => ?_
  have h0 : SetupKeep [.v28] s a :=
    ⟨fun r _ => congrFun ha.gpr r,fun r hr => ha.other r (by simpa using hr),
      ha.mem,ha.rd,ha.wr,ha.sp⟩
  refine ⟨((h0.trans (SetupKeep.ofConst hb.1)).trans (SetupKeep.ofConst hc.1)).trans
    (SetupKeep.ofConst ht.1),?_,?_,?_,ht.2⟩
  · rw [ht.1.vec .v28 (by decide),hc.1.vec .v28 (by decide),hb.1.vec .v28 (by decide),ha.v]
  · rw [ht.1.vec .v29 (by decide),hc.1.vec .v29 (by decide),hb.2]
  · rw [ht.1.vec .v24 (by decide),hc.2]


/-- All decomposition constants are initialized with the exact measured code. -/
theorem constants_ok (s : State) (g : Nat) :
    WP isa (.block (constants g)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23] s t ∧
      t.v .v16=repeatedWord (8380417) ∧
      t.v .v17=repeatedWord (127) ∧
      t.v .v18=repeatedWord (VG.Impl.MlDsa.AArch64.Round.dMul g) ∧
      t.v .v19=repeatedWord (2^(VG.Impl.MlDsa.AArch64.Round.dShift g-1)) ∧
      t.v .v20=repeatedWord (VG.Impl.MlDsa.AArch64.Round.dMod g) ∧
      t.v .v21=repeatedWord (2*g) ∧
      t.v .v22=repeatedWord (1) ∧
      t.v .v23=0 := by
  unfold constants
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok s .v16 _) fun a0 h0 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a0 .v17 _) fun a1 h1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a1 .v18 _) fun a2 h2 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a2 .v19 _) fun a3 h3 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a3 .v20 _) fun a4 h4 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a4 .v21 _) fun a5 h5 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok a5 .v22 _) fun a6 h6 => ?_
  refine wp_vop (d := .v23) rfl fun t ht => WP.block_nil_iff.mpr ?_
  have hk : SetupKeep [.v23] a6 t :=
    ⟨fun r _ => congrFun ht.gpr r,fun r hr => ht.other r (by simpa using hr),
      ht.mem,ht.rd,ht.wr,ht.sp⟩
  refine ⟨(((((((SetupKeep.ofConst h0.1).trans (SetupKeep.ofConst h1.1)).trans (SetupKeep.ofConst h2.1)).trans (SetupKeep.ofConst h3.1)).trans (SetupKeep.ofConst h4.1)).trans (SetupKeep.ofConst h5.1)).trans (SetupKeep.ofConst h6.1)).trans hk,?_,?_,?_,?_,?_,?_,?_,ht.v⟩
  · rw [ht.other .v16 (by decide), h6.1.vec .v16 (by decide), h5.1.vec .v16 (by decide), h4.1.vec .v16 (by decide), h3.1.vec .v16 (by decide), h2.1.vec .v16 (by decide), h1.1.vec .v16 (by decide), h0.2]
  · rw [ht.other .v17 (by decide), h6.1.vec .v17 (by decide), h5.1.vec .v17 (by decide), h4.1.vec .v17 (by decide), h3.1.vec .v17 (by decide), h2.1.vec .v17 (by decide), h1.2]
  · rw [ht.other .v18 (by decide), h6.1.vec .v18 (by decide), h5.1.vec .v18 (by decide), h4.1.vec .v18 (by decide), h3.1.vec .v18 (by decide), h2.2]
  · rw [ht.other .v19 (by decide), h6.1.vec .v19 (by decide), h5.1.vec .v19 (by decide), h4.1.vec .v19 (by decide), h3.2]
  · rw [ht.other .v20 (by decide), h6.1.vec .v20 (by decide), h5.1.vec .v20 (by decide), h4.2]
  · rw [ht.other .v21 (by decide), h6.1.vec .v21 (by decide), h5.2]
  · rw [ht.other .v22 (by decide), h6.2]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
