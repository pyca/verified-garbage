import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# x86-64: what a block leaves of the AVX-512 registers, lane by lane

`ZFrame rs s s'`: `s'` is `s` but for the vector registers `rs` (all four
128-bit lanes of each) and the flags, as `YFrame` states of two lanes. A
`ZFrame` is a `YFrame` (`ZFrame.yframe`).
-/

namespace VG.X86_64

/-- `s'` is `s` but for the vector registers `rs` (and the flags). -/
structure ZFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  zlane : ∀ r, r ∉ rs → ∀ l < 4, s'.zlane r l = s.zlane r l

theorem ZFrame.refl (rs : List XReg) (s : State) : ZFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem ZFrame.trans {rs : List XReg} {s s' s'' : State} (h : ZFrame rs s s') (h' : ZFrame rs s' s'') :
    ZFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr l hl => (h'.zlane r hr l hl).trans (h.zlane r hr l hl)⟩

theorem ZFrame.comp {rs rs' : List XReg} {s s' s'' : State} (h : ZFrame rs s s')
    (h' : ZFrame rs' s' s'') : ZFrame (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr l hl => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.zlane r hr.2 l hl).trans (h.zlane r hr.1 l hl)⟩

theorem ZFrame.mono {rs rs' : List XReg} {s s' : State} (h : ZFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    ZFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.zlane r fun h' => hr (hs r h')⟩

/-- Lanes 0 and 1 of `zlane` are `lane`'s. -/
theorem State.zlane_lt2 (s : State) (r : XReg) {l : Nat} (hl : l < 2) : s.zlane r l = s.lane r l := by
  simp only [State.zlane, hl, ite_true]

theorem ZFrame.yframe {rs : List XReg} {s s' : State} (h : ZFrame rs s s') : YFrame rs s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr l hl => by
    rw [← s'.zlane_lt2 r hl, ← s.zlane_lt2 r hl]; exact h.zlane r hr l (by omega)⟩

end VG.X86_64
