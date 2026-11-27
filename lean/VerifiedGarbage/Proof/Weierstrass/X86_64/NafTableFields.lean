module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableIO
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! ### `Weierstrass.X86_64.PointTransfer`, which this module and modules that import it used -/

section

/-! An exact field environment for point transfers through public addresses. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.X86_64

def pointTransferEnv {F : Type _} (E : Nat → F) (o q : Pt) (x : Nat) : F :=
  if x=o.x then E q.x else if x=o.y then E q.y else if x=o.z then E q.z else E x

theorem Inv.transferPointFields {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fin m} {s t : State}
    (hI : Inv M base size m Sl V E s)
    (hD : ∀ x∈jacCoords o, Sl x) (hQ : ∀ x∈jacCoords q, x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t) (ho : Outside base o.x (24*M.n) s.mem t.mem) :
    ProgKeep M base (jacCoords o) s t ∧
    Inv M base size m Sl (jacCoords o++V) (pointTransferEnv E o q) t := by
  have kp : ProgKeep M base (jacCoords o) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx o.x (by simp [jacCoords])
      have hx₁ := hx o.y (by simp [jacCoords])
      have hx₂ := hx o.z (by simp [jacCoords])
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega_using [hx₀, hx₁, hx₂]
  have hlt : ∀ x∈jacCoords o, wordsVal t.mem base x M.n<m := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
  have hi := hI.of_progKeep hL kp hD hlt
  refine ⟨kp,{hi with val := ?_}⟩
  intro x hx
  simp only [pointTransferEnv]
  split
  · subst x
    rw [vx,hI.val _ (hQ _ (by simp [jacCoords]))]
  · split
    · subst x
      rw [vy,hI.val _ (hQ _ (by simp [jacCoords]))]
    · split
      · subst x
        rw [vz,hI.val _ (hQ _ (by simp [jacCoords]))]
      · have hnot : x∉jacCoords o := by simp_all only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_false_eq_true]
        have hv : x∈V := (List.mem_append.mp hx).resolve_left hnot
        rw [kp.slot hL hI.scr hD (hI.sl x hv) hnot,hI.val x hv]

end VG.Proof.Weierstrass.X86_64

end

end

/-! Exact field values after the public odd-table store. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafTableFields_ok {K : WinCfg} {base : Addr} {size j m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9)
    (hy : K.R.y=K.R.x+8*K.M.n) (hz : K.R.z=K.R.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s)
    (hj : j<8) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+192*K.M.n≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)), Sl x)
    (hQ : ∀ x∈jacCoords K.R, x∈V)
    (hSep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      ProgKeep K.M base (jacCoords (K.tblPt (j+1))) s t ∧
      Inv K.M base size m Sl (jacCoords (K.tblPt (j+1))++V)
        (pointTransferEnv E (K.tblPt (j+1)) K.R) t := by
  have hrz := hL.le K.R.z (hI.sl _ (hQ _ (by simp [jacCoords])))
  rw [hz] at hrz
  refine WP.mono (nafTableStore_ok hI.scr hj hc hn ht hT (by omega_using [hrz]) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPointFields hL ?_ ?_ hD hQ ?_ ?_ ?_ hk ?_
  · simp only [WinCfg.tblPt]
  · simp only [WinCfg.tblPt]
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using hv 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using hv 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega_using []]
      using hv 2 (by decide)
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using ho

end VG.Proof.Weierstrass.X86_64
