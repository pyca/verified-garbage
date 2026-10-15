module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Shared
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

def sat (W : List (BitVec 64)) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 W
  rd := [⟨65536,512⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem sat_held {W : List (BitVec 64)} (hl : W.length=64) :
    ∀ i<64,(sat W).mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=W.getD i 0 := by
  intro i hi
  exact constMem_held 65536 W (by rw [hl]; decide) i (by rw [hl]; exact hi)

theorem sat_reduced {W : List (BitVec 64)} (hl : W.length=64) : Reduced (sat W).mem 4096 := by
  intro i hi
  simp only [sat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v:=(0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*W.length := by
      rw [hl]
      change i<256 at hi
      bv_omega
    simp only [constMem,ha,ite_false]
    simp only [BitVec.extractLsb'_zero]; rfl

theorem shared_pre_intro {s : State} (op : Poly → Poly) (symbol : String)
    (W : List (BitVec 64)) (hl : W.length=64)
    (hrd : s.rd=[⟨s.syms symbol,512⟩])
    (hwr : s.wr=[polyRegion (s.gpr .x0),polyRegion (s.gpr .x1)])
    (held : ∀ i<64,s.mem.readW (s.syms symbol+BitVec.ofNat 64 (8*i)) 64=W.getD i 0)
    (hfit : (s.syms symbol).toNat+512≤2^64)
    (hsep : ∀ r∈s.wr,(⟨s.syms symbol,512⟩:Region).Disjoint r)
    (hdisj : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1)))
    (hf : (s.gpr .x0).toNat+1024≤2^64) (hw : (s.gpr .x1).toNat+1024≤2^64)
    (hred : Reduced s.mem (s.gpr .x0)) :
    (inPlaceContract (abi.withConsts [(symbol,W)]) op).pre s := by
  sig_pre [inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
  simp only [hl,Nat.reduceMul]
  exact ⟨by rw [hrd]; rfl,held,hfit,hsep,by rw [hrd]; rfl,hwr,hdisj,hf,hw,hred⟩

theorem shared_sat (op : Poly → Poly) (symbol : String) (W : List (BitVec 64)) (hl : W.length=64) :
    (inPlaceContract (abi.withConsts [(symbol,W)]) op).pre (sat W) := by
  apply shared_pre_intro op symbol W hl rfl rfl (sat_held hl) (by change (65536:Nat)+512≤2^64; decide)
  · intro r hr
    change r∈[⟨4096,1024⟩,⟨8192,1024⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by change Region.sep _ _ = true; dsimp only [sat]; decide)
  · exact Region.disjoint_of_sep (by change Region.sep ⟨4096,1024⟩ ⟨8192,1024⟩ = true; decide)
  · change (4096:Nat)+1024≤2^64; decide
  · change (8192:Nat)+1024≤2^64; decide
  · exact sat_reduced hl

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
