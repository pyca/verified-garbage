module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectKey
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Table
import VerifiedGarbage.Proof.Framework.Block

/-! The directly indexed odd-key operand preserves bounded field slots. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.AArch64.Window (dst tw TPt)
open VG.Proof.Ed448.WnafWide (oddPoint)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem keyOperand_ok {s:State} {base:Addr} {P:Spec.Ed448.Point}
    (hs:Scr s base) (hb:BEnv s.mem base) (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(tw s.mem base e w).toNat<Mb) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block VG.Impl.Ed448.AArch64.Sparse.selectKey) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [6,7,8] s.mem t.mem ∧
      Bnd Mb t.mem base (slot 6) ∧ pt (EV t.mem base) 6 7 8=oddPoint P (m/2) ∧
      VG.Proof.X448.AArch64.Keeps [.x11,.x8,.x9,.x4] s t := by
  refine WP.mono (selectKey_ok hs hm h11) fun t ⟨tv,fo,kt⟩ => ?_
  have sm:Same base [6,7,8] s.mem t.mem:=by
    intro i hi j hj
    have n6:i.val≠6:=fun h => hi (by rw [show i=(6:Index) from Fin.ext h];decide)
    have n7:i.val≠7:=fun h => hi (by rw [show i=(7:Index) from Fin.ext h];decide)
    have n8:i.val≠8:=fun h => hi (by rw [show i=(8:Index) from Fin.ext h];decide)
    have hilt:=i.isLt
    exact fo.limbs (by simp only [slot];omega) (by simp only [slot];omega) (by omega)
  have cw:∀ c<3,∀ j<8,word t.mem base (slot (6+c)+8*j)=tw s.mem base (m/2) (8*c+j):=by
    intro c hc j hj
    have hd:dst (8*c+j)=slot (6+c)+8*j:=by simp only [dst,slot];omega
    rw [←hd,tv _ (by omega)]
  have tb:BEnv t.mem base:=by
    intro i j hj
    by_cases hi:i∈[(6:Index),7,8]
    · have he:i.val=6 ∨ i.val=7 ∨ i.val=8:=by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> simp
      have hr:slot i.val=slot (6+(i.val-6)):=by congr 1;omega
      show (word t.mem base (slot i.val+8*j)).toNat<Ib
      rw [hr,cw _ (by omega) j hj]
      exact (ht (m/2) (by omega)).2 _ (by omega)
    · rw [sm i hi j hj]
      exact hb i j hj
  refine ⟨⟨kt.mono (by decide),fun x hx _ => fo x (by omega)⟩,tb,sm,?_,?_,kt⟩
  · intro j hj
    show (word t.mem base (slot 6+8*j)).toNat<Mb
    rw [cw 0 (by decide) j hj]
    simpa only [Nat.mul_zero,Nat.zero_add] using hxb (m/2) (by omega) j hj
  · rw [←(ht (m/2) (by omega)).1]
    symm
    unfold TPt pt
    refine Spec.Ed448.Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=0) (by omega) (fun j hj => (cw 0 (by decide) j hj).symm)
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=1) (by omega) (fun j hj => (cw 1 (by decide) j hj).symm)
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=2) (by omega) (fun j hj => (cw 2 (by decide) j hj).symm)

end VG.Proof.Ed448.AArch64.Sparse
