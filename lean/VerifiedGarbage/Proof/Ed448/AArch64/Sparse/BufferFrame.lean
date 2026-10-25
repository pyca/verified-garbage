module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Iter
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.X448.AArch64.Mem

/-! The two public digit buffers are disjoint from field slots, key entries,
challenge bytes and the verifier's saved state. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Proof.X448.AArch64 (Outside off ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem buffer_env {base:Addr} {m m':Mem} {o n:Nat} (h:Outside base o n m m') (ho:2880≤o) :
    EV m' base=EV m base:=by
  funext i
  have hi:=i.isLt
  exact Window.FV_of_limbs fun j hj => h.limbs (Or.inl (by simp only [slot];omega))
    (by simp only [slot];omega) (by omega)

theorem buffer_bounds {base:Addr} {m m':Mem} {o n:Nat} (h:Outside base o n m m')
    (ho:2880≤o) (hb:BEnv m base) : BEnv m' base:=by
  intro i j hj
  have hi:=i.isLt
  rw [h.limbs (Or.inl (by simp only [slot];omega)) (by simp only [slot];omega) (by omega)]
  exact hb i j hj

theorem buffer_table {base:Addr} {m m':Mem} {o n:Nat} (h:Outside base o n m m')
    (ho:o+n≤TAB ∨ TAB+1536≤o) {P:Spec.Ed448.Point} (ht:OddTabOk m base P 8) : OddTabOk m' base P 8:=by
  have hm:∀ e<8,∀ w<24,Window.tw m' base e w=Window.tw m base e w:=by
    intro e he w hw
    exact h.word (by omega) (by simp only [TAB];omega)
  intro e he
  refine ⟨?_,fun w hw => ?_⟩
  · rw [Window.TPt_of_tw (hm e he)]
    exact (ht e he).1
  · rw [hm e he w hw]
    exact (ht e he).2 w hw

theorem buffer_xbounds {base:Addr} {m m':Mem} {o n:Nat} (h:Outside base o n m m')
    (ho:o+n≤TAB ∨ TAB+1536≤o)
    (hx:∀ e<8,∀ w<8,(Window.tw m base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb) :
    ∀ e<8,∀ w<8,(Window.tw m' base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb:=by
  intro e he w hw
  rw [Window.tw,h.word (by omega) (by simp only [TAB];omega)]
  exact hx e he w hw

theorem buffer_bytes {base:Addr} {m m':Mem} {o n d k:Nat} (h:Outside base o n m m')
    (ho:d+k≤o ∨ o+n≤d) (hd:d+k≤8192) :
    Spec.Ed448.bytesAt m' (off base d) k=Spec.Ed448.bytesAt m (off base d) k:=by
  unfold Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi':i<k:=List.mem_range.mp hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)

theorem buffer_baseTable {base p:Addr} {s t:State} {o n:Nat} (h:Outside base o n s.mem t.mem)
    (ho:o+n≤8192) (hr:t.rd++t.wr=s.rd++s.wr) (ht:BaseTableAt s base p) : BaseTableAt t base p:=by
  refine ⟨hr ▸ ht.read,ht.far,fun i hi => ?_⟩
  rw [←ht.val i hi]
  apply Mem.readW_congr
  intro j hj
  have he:p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j=p+BitVec.ofNat 64 (8*i+j):=
    Offset.add_add _ _ _
  rw [he]
  exact h _ (Or.inr (Nat.le_trans ho (ht.far _ (by omega))))

end VG.Proof.Ed448.AArch64.Sparse
