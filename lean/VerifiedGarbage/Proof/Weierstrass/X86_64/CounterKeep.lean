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

end VG.Proof.Weierstrass.X86_64
