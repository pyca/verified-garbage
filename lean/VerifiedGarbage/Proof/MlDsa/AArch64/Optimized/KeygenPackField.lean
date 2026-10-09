import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def fieldValue (v : VReg → BitVec 128) (j : Nat) : BitVec 64 :=
  (vword (v (if j<4 then .v0 else .v1)) (j%4)).setWidth 64

def joined (d j : Nat) (acc value : BitVec 64) : BitVec 64 :=
  if d*j%64=0 then value else acc ||| (value <<< (d*j%64))

def fieldAcc (d j : Nat) (acc value : BitVec 64) : BitVec 64 :=
  if d*j%64+d>64 then value >>> (64-d*j%64) else joined d j acc value

def fieldMem (d j : Nat) (m : Mem) (out : Addr) (acc value : BitVec 64) : Mem :=
  if d*j%64+d≥64 then m.writeW (out+BitVec.ofNat 64 (d*j/64*8)) (joined d j acc value) else m

theorem field_ok (d j : Nat) (hd : d≤20) (hj : j<8) (s : State)
    (hw : d*j%64+d≥64 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (d*j/64*8)) 8) :
    WP isa (.block (field d j)) s fun t =>
      ((t.gpr .x9=fieldAcc d j (s.gpr .x9) (fieldValue s.v j) ∧
        t.mem=fieldMem d j s.mem (s.gpr .x2) (s.gpr .x9) (fieldValue s.v j)) ∧
       Keep [.x9,.x10,.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by dsimp only [field]; split_ifs <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by dsimp only [field]; split_ifs <;> rfl) (hv:=by dsimp only [field]; split_ifs <;> rfl)
  have hs : d*j%64<64 := Nat.mod_lt _ (by decide)
  have hj4 : j%4<4 := Nat.mod_lt _ (by decide)
  have hidx : j%4*32<128 := by omega
  have hd64 : ¬64≤d := by omega
  have hd64' : ¬64<d := by omega
  have hprod : d*j≤20*7 := Nat.mul_le_mul hd (by omega)
  have ho : d*j/64*8<4096*8 := by omega
  have ho8 : d*j/64*8%8=0 := by omega
  by_cases hzero : d*j%64=0
  · by_cases hfull : d*j%64+d≥64
    · omega
    · have hnot : ¬d*j%64+d>64 := by omega
      simp only [field,hzero,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
      arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,Nat.zero_add,hd64,hd64']
  · by_cases hfull : d*j%64+d≥64
    · by_cases hcross : d*j%64+d>64
      · have hshift : 64-d*j%64<64 := by omega
        simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
        arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hw hfull,hs,ho,ho8,hshift]
      · simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
        arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hw hfull,hs,ho,ho8]
    · have hcross : ¬d*j%64+d>64 := by omega
      simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
      arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hs]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
