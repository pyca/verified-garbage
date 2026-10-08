import VerifiedGarbage.Proof.Weierstrass.X86.WinJacTableStore

/-! The memory and register frame shared by table construction and the secret loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def clobbers : List Reg := clob++[.esi]

structure Frame (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs clobbers s₀ s
  unch : Unch base (allW K wk) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base

theorem ro_apart {K : JacWinCfg} {size wk m : Nat} (hL : Layout K size wk)
    (hW : WkOk K.F K.M m size wk (·∈slots K)) {x : Nat} (hx : x∈ro K) :
    ∀ w∈allW K wk,x+8*K.M.n≤w.1 ∨ w.1+w.2≤x := by
  have hxs : x∈slots K := List.mem_append_left _ hx
  intro w hw
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨y,hy,rfl⟩ | rfl | rfl | rfl) | rfl
  · exact hL.lay.apart x y hxs (List.mem_append_right _ hy) (fun he => hL.readonly x hx (he ▸ hy))
  · exact hL.lay.tmp x hxs
  · exact Or.inl (hW.sl x hxs)
  · have := hL.lay.le x hxs
    have := hL.size_le
    change _≤8192 ∨ _
    omega
  · have := hL.low x hxs
    dsimp only
    rw [hL.n]
    omega

theorem mod_unch {K : JacWinCfg} {base : Addr} {size wk m : Nat} (hL : Layout K size wk)
    (hW : WkOk K.F K.M m size wk (·∈slots K)) {s t : State}
    (hs : Scr s base size) (hM : ModOkW K.M size m s.mem base)
    (hu : Unch base (allW K wk) s.mem t.mem) : ModOkW K.M size m t.mem base := by
  refine ⟨hM.n0,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red⟩
  rw [hu.wordsVal (fun w hw => ?_) (by have := hs.nowrap; have := hM.mo; omega),hM.val]
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨x,hx,rfl⟩ | rfl | rfl | rfl) | rfl
  · exact (hL.lay.mo x (List.mem_append_right _ hx)).symm
  · exact hM.sep
  · exact Or.inl hW.mo
  · have := hM.mo
    have := hL.size_le
    change _≤8192 ∨ _
    omega
  · have := hW.mo
    have := hL.wk_end
    dsimp only
    rw [hL.n] at *
    omega

theorem Frame.refl {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat} {s : State}
    (hs : Scr s base size) (hm : ModOkW K.M size C.p s.mem base) : Frame K C base size wk s s :=
  ⟨hs,⟨fun _ _ => rfl,rfl,rfl⟩,Unch.refl _ _ _,hm⟩

theorem Frame.next {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hs : Scr t base size)
    (hk : KeepRegs clobbers s t) (hu : Unch base (allW K wk) s.mem t.mem) :
    Frame K C base size wk s₀ t :=
  ⟨hs,⟨fun r hr => (hk.gpr r hr).trans (h.keep.gpr r hr),hk.rd.trans h.keep.rd,hk.wr.trans h.keep.wr⟩,
    (h.unch.trans hu).mono (fun _ hw => (List.mem_append.mp hw).elim id id),mod_unch hL hW h.scr h.mod hu⟩

theorem Frame.ro {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) {x : Nat} (hx : x∈ro K) :
    wordsVal s.mem base x K.M.n=wordsVal s₀.mem base x K.M.n :=
  h.unch.wordsVal (ro_apart hL hW hx) (by
    have := h.scr.nowrap
    have := hL.lay.le x (List.mem_append_left _ hx)
    omega)

theorem Frame.bits {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) {s₀ s : State} (h : Frame K C base size wk s₀ s) {i : Nat} (hi : i<260) :
    s.mem (off base (K.bits+i))=s₀.mem (off base (K.bits+i)) := by
  have ht := hL.table
  have hb := hL.bits
  have hn := h.scr.nowrap
  apply h.unch.byte (fun w hw => ?_) (by omega)
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨x,hx,rfl⟩ | rfl | rfl | rfl) | rfl
  · have := hL.bits_low x hx
    dsimp only
    rw [hL.n]
    omega
  · have := hL.bits_tmp
    dsimp only
    rw [hL.n]
    omega
  · have := hL.bits_wk
    dsimp only
    rw [hL.n]
    omega
  · have := hL.size_le
    change _<8192 ∨ _
    omega
  · dsimp only
    omega

theorem field_allW {K : JacWinCfg} {base : Addr} {wk : Nat} {W : List Nat} {s t : State}
    (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K) :
    Unch base (allW K wk) s.mem t.mem :=
  hk.unch.mono fun w h => List.mem_append_left _ (progW_mono hw w h)

theorem Frame.field {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) {W : List Nat}
    (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K) : Frame K C base size wk s₀ t :=
  h.next hL hW (hk.scr h.scr)
    ⟨fun r hr => hk.gpr r (fun hc => hr (List.mem_append_left _ hc)),hk.rd,hk.wr⟩ (field_allW hk hw)


theorem Frame.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hk : CKeeps [.esi] s t) :
    Frame K C base size wk s₀ t := by
  refine ⟨h.scr.of_keeps hk.keeps (by decide),
    h.keep.trans ((CKeeps.regs hk).mono (fun _ hr => List.mem_append_right _ hr)),?_,?_⟩
  · rw [hk.2.1]; exact h.unch
  · rw [hk.2.1]; exact h.mod

theorem mov_counter_ok (s : State) (m : Nat) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 m))]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 m ∧ CKeeps [.esi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => by
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

/-- Storing an entry changes only the packed table, within the shared frame. -/
theorem store_allW {K : JacWinCfg} {base : Addr} {wk m : Nat} {s t : State}
    (hm : m<16) (hu : Unch base (storeW K m) s.mem t.mem) :
    Unch base (allW K wk) s.mem t.mem := by
  apply hu.cover
  intro w hw
  refine ⟨(K.tbl,2560),List.mem_append_right _ (List.mem_singleton_self _),?_⟩
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> constructor <;> omega

theorem Frame.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hu : Unch base (storeW K m) s.mem t.mem) (hk : KeepRegs [.eax,.ecx,.edx] s t) :
    Frame K C base size wk s₀ t := by
  apply h.next hL hW (h.scr.of_keepRegs hk (by decide)) ?_ (store_allW hm hu)
  refine ⟨fun r hr => hk.gpr r ?_,hk.rd,hk.wr⟩
  intro he
  apply hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> decide

/-- Compose table growth with the frame needed by subsequent arithmetic. -/
theorem store_framed_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk M : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hM : M<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (M+1)) {P : Point C}
    (hOld : Table K C base P M s)
    (hNew : Cached C base s (fun c => K.T+32*c) (mul (M+1) P)) :
    WP isa (.block K.storeEntry) s fun t =>
      Table K C base P (M+1) t ∧ Frame K C base size wk s₀ t ∧
      t.gpr .esi=BitVec.ofNat 32 (M+1) := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work,JacWinCfg.z3])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (store_table_ok h.scr hM hb hL.table hT hOld hNew)
    fun t ⟨ht,hu,hk⟩ => ⟨ht,h.store hL hW hM hu hk,(hk.gpr _ (by decide)).trans hb⟩

end VG.Proof.Weierstrass.X86.JWin
