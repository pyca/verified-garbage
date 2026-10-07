import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! Field-operation frames while RBX temporarily holds a public loop counter. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

structure CounterKeep (M : Mod) (base : Addr) (W : List Nat) (s t : State) : Prop where
  regs : KeepRegs (clob M.n++[.rbx]) s t
  mem : ∀ x, (∀ w∈W,ofs base x<w ∨ w+8*M.n≤ofs base x) →
    (ofs base x<M.tmp ∨ M.tmp+8*M.n≤ofs base x) → t.mem x=s.mem x

theorem CounterKeep.of_progKeep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep M base W s t) : CounterKeep M base W s t :=
  ⟨⟨fun r hr => h.gpr r (fun hh => hr (List.mem_append_left _ hh)),h.rd,h.wr⟩,h.mem⟩

theorem CounterKeep.of_keeps {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : Keeps [.rbx] s t) : CounterKeep M base W s t :=
  ⟨⟨fun r hr => h.1 r (fun hh => hr (List.mem_append_right _ hh)),h.2.2.1,h.2.2.2⟩,
    fun x _ _ => congrFun h.2.1 x⟩

theorem CounterKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) :
    CounterKeep M base W s s := .of_progKeep (.refl M base W s)

theorem CounterKeep.trans {M : Mod} {base : Addr} {W : List Nat} {s t u : State}
    (h : CounterKeep M base W s t) (h' : CounterKeep M base W t u) : CounterKeep M base W s u :=
  ⟨h.regs.trans h'.regs,fun x hx ht => (h'.mem x hx ht).trans (h.mem x hx ht)⟩

theorem CounterKeep.mono {M : Mod} {base : Addr} {W W' : List Nat} {s t : State}
    (h : CounterKeep M base W s t) (hw : ∀ x∈W,x∈W') : CounterKeep M base W' s t :=
  ⟨h.regs,fun x hx ht => h.mem x (fun w hh => hx w (hw w hh)) ht⟩

theorem CounterKeep.progKeep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : CounterKeep M base W s t) (hb : t.gpr .rbx=s.gpr .rbx) : ProgKeep M base W s t := by
  refine ⟨fun r hr => ?_,h.regs.rd,h.regs.wr,h.mem⟩
  by_cases he : r=.rbx
  · subst r
    exact hb
  · exact h.regs.gpr r (by simpa only [List.mem_append,List.mem_singleton,not_or] using And.intro hr he)

theorem CounterKeep.unch {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : CounterKeep M base W s t) :
    Unch base (W.map (·,8*M.n)++[(M.tmp,8*M.n)]) s.mem t.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem CounterKeep.slot {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    {W : List Nat} {s t : State} (h : CounterKeep M base W s t)
    (hL : Lay M size Sl) (hs : Scr s base size) (hW : ∀ x∈W,Sl x)
    {x : Nat} (hx : Sl x) (hnot : x∉W) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
  apply h.unch.wordsVal _ (by have := hL.le x hx; have := hs.nowrap; omega)
  intro w hw
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩|rfl
  · exact hL.apart x y hx (hW y hy) (fun he => hnot (he ▸ hy))
  · exact hL.tmp x hx

theorem CounterKeep.field_eq {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V V' W : List Nat} {E F : Nat → Fin m} {s t : State}
    (h : CounterKeep M base W s t) (hL : Lay M size Sl)
    (hs : Inv M base size m Sl V E s) (ht : Inv M base size m Sl V' F t)
    (hW : ∀ x∈W,Sl x) {x : Nat} (hv : x∈V) (hv' : x∈V') (hnot : x∉W) : F x=E x := by
  rw [←ht.val x hv',h.slot hL hs.scr hW (hs.sl x hv) hnot,hs.val x hv]

end VG.Proof.Weierstrass.X86_64
