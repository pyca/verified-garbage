import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables

/-! Initialize the shared accumulator and its carry-digit counter. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

theorem jointCounter_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 256)]) s fun t => t.gpr .rbx=256 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

theorem jointSeed_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow C G} {s : State}
    (hL : JointLayout c size) (hOne : c.K.one<C.p)
    (hi : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base s) s)
    (hs : JointStable c C base Q u v s) (he : JointGenerator c C base T size row s) :
    WP isa (.block (Jacobian.infinity c.K c.K.R++([.mov32 .rbx (.imm 256)] : List Instr))) s fun t =>
      JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) .infinity t ∧ t.gpr .rbx=256 := by
  rw [WP.block_append_iff]
  have hR : ∀ x∈jacCoords c.K.R,x∈jointSlots c := fun x hx => hi.sl x (jointLive_R c x hx)
  refine WP.mono_syms (infinityPoint_ok hL.lay hR hi hOne) fun a ⟨ea,ka,ia,pa⟩ sa => ?_
  have kw : ProgKeep c.K.M base (jointWork c) s a := ka.mono (by
    intro x hx
    simp only [rcbW,jointWork,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind)
  have ca : JointCore c C base size Q u v (JointGenerator c C base T size row) .infinity a :=
    ⟨(ia.sub (fun _ hx => List.mem_append_right _ hx)).to_tmv,
      hs.keep hL.n kw (fun r hr => by
        have := hL.stableBounds r hr; have := hi.scr.nowrap; omega) hL.stableSep,
      JointGenerator.workKeep hL hi.mod.tmp s a kw sa he,
      ia.point_tmv (fun _ hx => List.mem_append_left _ hx) pa⟩
  refine WP.mono_syms (jointCounter_ok a) fun t ⟨tb,kt⟩ st => ?_
  exact ⟨(JointLoopKeep.of_prog kw).trans (JointLoopKeep.of_keeps kt),
    ca.of_keeps kt (by decide) (fun n hn hn' ho => (ca.external n hn hn' ho).of_keeps kt st),tb⟩

theorem JointLoopKeep.mono {M : Mod} {base : Addr} {W W' : List Nat} {s t : State}
    (h : JointLoopKeep M base W s t) (hw : ∀ w∈W,w∈W') : JointLoopKeep M base W' s t :=
  ⟨h.regs,h.unch.mono (by
    intro w hm
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hm ⊢
    rcases hm with ⟨x,hx,rfl⟩|rfl
    · exact Or.inl ⟨x,hw x hx,rfl⟩
    · exact Or.inr rfl)⟩

end VG.Proof.Weierstrass.X86_64
