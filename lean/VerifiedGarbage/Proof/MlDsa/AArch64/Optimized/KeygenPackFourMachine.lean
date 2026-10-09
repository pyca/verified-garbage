import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def fourGather (v : VReg → BitVec 128) (idx : BitVec 128) : BitVec 128 :=
  ofVBytes fun i=>let j:=(vbyte idx i).toNat; if j<64 then tableByte v .v0 j else 0

def fourShift (x : BitVec 128) (n : Nat) : BitVec 128 :=
  VArr.s4.map2 (fun _ _ y=>y >>> n) x x

def fourCompress (x mask idx : BitVec 128) : BitVec 128 :=
  let a := (x ||| fourShift x 4) &&& mask
  let b := a ||| fourShift a 8
  ofVBytes fun i=>let j:=(vbyte idx i).toNat; if j<16 then vbyte b j else 0

def fourShuffle : List Instr :=
  [.vop (.tblN false 4 .v0 .v0 .v18),.vop (.shift .ushr .s4 .v1 .v0 4),
   .vop (.logic .orr .v0 .v0 .v1),.vop (.logic .and .v0 .v0 .v20),
   .vop (.shift .ushr .s4 .v1 .v0 8),.vop (.logic .orr .v0 .v0 .v1),
   .vop (.tbl .v0 .v0 .v19)]

theorem fourShuffle_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v0,.v1] s t →
      t.v .v0=fourCompress (fourGather s.v (s.v .v18)) (s.v .v20) (s.v .v19) →
      WP isa (.block rest) t Q) :
    WP isa (.block (fourShuffle++rest)) s Q := by
  refine wp_vop (d:=.v0) rfl fun a ha=>wp_vop (d:=.v1) rfl fun b hb=>
    wp_vop (d:=.v0) rfl fun c hc=>wp_vop (d:=.v0) rfl fun d hd=>
    wp_vop (d:=.v1) rfl fun e he=>wp_vop (d:=.v0) rfl fun f hf=>
    wp_vop (d:=.v0) rfl fun t ht=>?_
  refine k t (((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans he.chg).trans hf.chg).trans ht.chg).mono (by simp)) ?_
  rw [ht.v,hf.v,he.get .v0 (by decide),he.v,hd.v,hc.v,hb.get .v0 (by decide),hb.v,ha.v,
    hf.get .v19 (by decide),he.get .v19 (by decide),hd.get .v19 (by decide),hc.get .v19 (by decide),
    hb.get .v19 (by decide),ha.get .v19 (by decide),hc.get .v20 (by decide),hb.get .v20 (by decide),ha.get .v20 (by decide)]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
