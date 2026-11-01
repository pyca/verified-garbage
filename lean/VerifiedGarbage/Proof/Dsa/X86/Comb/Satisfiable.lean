module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.ABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable

/-! Concrete small-modulus witnesses satisfy both helper contracts.

The witness holds the modulus 3, the base 1 and the context the spec
defines for them; its numbers are read back by lemmas, not evaluated. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic

/-- The context words for modulus 3 and base 1. -/
def satContext (n e : Nat) : List (BitVec 64) := Proof.Dsa.FixedBaseComb.context (layout n e) 3 1

def satMem (n e : Nat) (a : Addr) : Byte :=
  let p := a.toNat
  if 0xf0000004≤p ∧ p<0xf0000008 then BitVec.ofNat 8 (0x10000/256^(p-0xf0000004))
  else if 0xf0000008≤p ∧ p<0xf000000c then BitVec.ofNat 8 (((layout n e).size/8)/256^(p-0xf0000008))
  else if p<0x10000 then 0
  else let o := p-0x10000
    if slot n 0≤o ∧ o<slot n 0+8*n then BitVec.ofNat 8 (3/256^(o-slot n 0))
    else if slot n 5≤o ∧ o<slot n 5+8*n then BitVec.ofNat 8 (1/256^(o-slot n 5))
    else if context n≤o ∧ o<context n+272*n then
      BitVec.ofNat 8 (((satContext n e).getD ((o-context n)/8) 0).toNat/256^((o-context n)%8))
    else 0

def satState (n e : Nat) : State where
  gpr r := if r=.esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem n e
  rd := [⟨0xf0000004,8⟩]
  wr := [⟨0x10000,(layout n e).size⟩]

theorem read_bytes (m : Mem) : ∀ (k : Nat) (a : Addr) (x : Nat),
    (∀ j<k, m (a+BitVec.ofNat 64 j)=BitVec.ofNat 8 (x/256^j)) → (m.read a k).toNat=x%256^k
  | 0, _, _, _ => by simp only [Mem.read,BitVec.toNat_ofNat,Nat.pow_zero,Nat.mod_one]
  | k+1, a, x, h => by
    have h0 := h 0 (by omega)
    rw [BitVec.add_zero,Nat.pow_zero,Nat.div_one] at h0
    rw [Mont.read_toNat_succ,read_bytes m k (a+1) (x/256) (fun j hj => ?_),h0,BitVec.toNat_ofNat]
    · rw [show 256^(k+1)=2^8*256^k by rw [Nat.pow_succ,Nat.mul_comm],Nat.mod_mul]
    · rw [show a+1+BitVec.ofNat 64 j=a+BitVec.ofNat 64 (j+1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega,
        h (j+1) (by omega),Nat.pow_succ',Nat.div_div_eq_div_mul]

theorem toNat_add_ofNat {a : Addr} {j : Nat} (h : a.toNat+j<2^64) :
    (a+BitVec.ofNat 64 j).toNat=a.toNat+j := by
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- What the layout's offsets are, for `omega`. -/
theorem sat_bounds {n e : Nat} (supported : Supported n e) :
    1≤n ∧ slot n 0=64 ∧ slot n 5=104+80*n ∧ 104+88*n≤context n ∧
      0x10000+context n+272*n<0xf0000000 := by
  rcases supported with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem satMem_at {n e : Nat} {o : Nat} (ho : 0x10000+o<0xf0000000) :
    satMem n e (0x10000+BitVec.ofNat 64 o)=
      if slot n 0≤o ∧ o<slot n 0+8*n then BitVec.ofNat 8 (3/256^(o-slot n 0))
      else if slot n 5≤o ∧ o<slot n 5+8*n then BitVec.ofNat 8 (1/256^(o-slot n 5))
      else if context n≤o ∧ o<context n+272*n then
        BitVec.ofNat 8 (((satContext n e).getD ((o-context n)/8) 0).toNat/256^((o-context n)%8))
      else 0 := by
  have t : ((0x10000 : Addr)+BitVec.ofNat 64 o).toNat=0x10000+o := toNat_add_ofNat (by simp; omega)
  simp only [satMem,t]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),Nat.add_sub_cancel_left]

theorem toNat_off {o j : Nat} (_h : 0x10000+o+j<2^64) :
    ((0x10000 : Addr)+BitVec.ofNat 64 o+BitVec.ofNat 64 j)=0x10000+BitVec.ofNat 64 (o+j) := by
  rw [BitVec.add_assoc,BitVec.ofNat_add]

theorem sat_modulus {n e : Nat} (supported : Supported n e) :
    Proof.Dsa.ModPow.numAt (satMem n e) 0x10000 (slot n 0) (8*n)=3 := by
  obtain ⟨n1,s0,s5,c1,c2⟩ := sat_bounds supported
  unfold Proof.Dsa.ModPow.numAt
  rw [read_bytes _ _ _ 3 (fun j hj => ?_)]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show _<256^1 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  · rw [toNat_off (by omega),satMem_at (by omega),ite_eq_left (by omega),Nat.add_sub_cancel_left]

theorem sat_base {n e : Nat} (supported : Supported n e) :
    Proof.Dsa.ModPow.numAt (satMem n e) 0x10000 (slot n 5) (8*n)=1 := by
  obtain ⟨n1,s0,s5,c1,c2⟩ := sat_bounds supported
  unfold Proof.Dsa.ModPow.numAt
  rw [read_bytes _ _ _ 1 (fun j hj => ?_)]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show _<256^1 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  · rw [toNat_off (by omega),satMem_at (by omega),ite_eq_right (by omega),ite_eq_left (by omega),
      Nat.add_sub_cancel_left]

theorem satContext_length {n e : Nat} : (satContext n e).length=34*n := by
  simp only [satContext,Proof.Dsa.FixedBaseComb.context,List.length_append,
    Proof.Rsa.FixedBaseComb.toWords_length,Proof.Rsa.FixedBaseComb.table_length,layout,VG.Impl.Dsa.X86.Pow.layout]
  omega

theorem sat_context {n e : Nat} (supported : Supported n e) :
    Spec.Rsa.wordsAt (satMem n e) (0x10000+BitVec.ofNat 64 (context n)) (34*n)=satContext n e := by
  obtain ⟨n1,s0,s5,c1,c2⟩ := sat_bounds supported
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range,satContext_length]
  intro i hi _
  simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range] at hi
  simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.readW,BitVec.toNat_setWidth,Nat.reduceDiv]
  rw [read_bytes _ _ _ ((satContext n e).getD i 0).toNat (fun j hj => ?_)]
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [satContext_length]; omega),Option.getD_some]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (show 2^64≤256^8 by decide)),
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  · rw [toNat_off (by omega),toNat_off (by omega),satMem_at (by omega),ite_eq_right (by omega),
      ite_eq_right (by omega),ite_eq_left (by omega),show (context n+8*i+j-context n)/8=i by omega,
      show (context n+8*i+j-context n)%8=j by omega]

theorem sat_ws {n e : Nat} (supported : Supported n e) :
    BitVec.setWidth 64 (arg (satState n e) 0)=0x10000 := by
  rcases supported with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel

theorem satisfiable {n e : Nat} (supported : Supported n e) (prepare : Bool) :
    ∃ s, (contract prepare n e).pre s := by
  refine ⟨satState n e,?_⟩
  have valid := layout_valid supported
  have hm := sat_modulus supported
  have hb := sat_base supported
  have hc := sat_context supported
  have hw := sat_ws supported
  rcases supported with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases prepare
  all_goals
    sig_pre [contract,Proof.Dsa.FixedBaseComb.prepareContract,Proof.Dsa.FixedBaseComb.powerContract,
      Proof.Dsa.FixedBaseComb.arithmeticPre,Proof.Dsa.ModPow.sig,layout,VG.Impl.Dsa.X86.Pow.layout,
      abi,argSlots,argVal,argBytes,stackBelow]
    sig_and_intros
  all_goals try exact Region.disjoint_of_sep (by decide)
  all_goals try exact valid
  all_goals try unfold Proof.Dsa.FixedBaseComb.contextAt
  all_goals try rw [hw]
  all_goals simp only [Nat.reduceMul] at hm hb hc
  all_goals try rw [hm]
  all_goals try (dsimp only; rw [hm,hb]; exact hc)
  all_goals decide +kernel

end VG.Proof.Dsa.X86.Comb
