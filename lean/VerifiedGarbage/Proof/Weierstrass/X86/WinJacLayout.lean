import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! Low field slots and the packed table above the field-call workspace. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

def ro (K : JacWinCfg) : List Nat := [K.S.a,K.S.b3,K.P.x,K.P.y,K.P.z,K.zero]
def temps (K : JacWinCfg) : List Nat := [K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5]
def work (K : JacWinCfg) : List Nat := temps K ++
  [K.R.x,K.R.y,K.R.z,K.D.x,K.D.y,K.D.z,K.E.x,K.E.y,K.E.z,K.z2,K.z3,K.neg]
def slots (K : JacWinCfg) : List Nat := ro K ++ work K

def loopW (K : JacWinCfg) (wk : Nat) : List (Nat × Nat) := progW K.M wk (work K)
def allW (K : JacWinCfg) (wk : Nat) : List (Nat × Nat) := loopW K wk ++ [(K.tbl,2560)]

structure Layout (K : JacWinCfg) (size wk : Nat) : Prop where
  n : K.M.n=4
  size_le : size≤8192
  lay : Lay K.M size (·∈slots K)
  nd : (work K).Nodup
  readonly : ∀ x∈ro K,x∉work K
  table : K.tbl+2560≤size
  low : ∀ x∈slots K,x+32≤K.tbl
  tmp : K.M.tmp+32≤K.tbl
  wk_end : wk+256≤K.tbl
  bits : K.bits+260≤K.tbl
  bits_low : ∀ x∈work K,x+32≤K.bits
  bits_tmp : K.M.tmp+32≤K.bits
  bits_wk : wk+256≤K.bits
  J : 2≤K.J ∧ K.J≤52

theorem entry_bounds {K : JacWinCfg} {m c : Nat} (hm : m<16) (hc : c<5) :
    K.tbl≤K.entry m c ∧ K.entry m c+32≤K.tbl+2560 := by
  unfold JacWinCfg.entry
  split <;> omega

theorem entry_apart {K : JacWinCfg} {m n c d : Nat} (hm : m<16) (hn : n<16)
    (hc : c<5) (hd : d<5) (hne : m≠n ∨ c≠d) :
    K.entry m c+32≤K.entry n d ∨ K.entry n d+32≤K.entry m c := by
  unfold JacWinCfg.entry
  split <;> split <;> omega

/-- A field program cannot modify a cached table coordinate above its workspace. -/
theorem field_keep_entry {K : JacWinCfg} {base : Addr} {size wk : Nat} (hL : Layout K size wk)
    {s t : State} {W : List Nat} (hs : Scr s base size) (hk : ProgKeep K.M base wk W s t)
    (hW : ∀ x∈W,x∈work K) {m c : Nat} (hm : m<16) (hc : c<5) :
    wordsVal t.mem base (K.entry m c) 4=wordsVal s.mem base (K.entry m c) 4 := by
  have he := entry_bounds (K:=K) hm hc
  have ht := hL.table
  have hn := hs.nowrap
  apply hk.unch.wordsVal (d:=K.entry m c) (k:=4) (fun w hw => ?_) (by omega)
  simp only [progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
  · have := hL.low x (List.mem_append_right _ (hW x hx))
    dsimp only
    rw [hL.n]
    omega
  · have := hL.tmp
    dsimp only
    rw [hL.n]
    omega
  · have := hL.wk_end
    dsimp only
    rw [hL.n]
    omega
  · have := hL.size_le
    change _≤8192 ∨ _
    omega

end VG.Proof.Weierstrass.X86.JWin
