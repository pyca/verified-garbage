module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Two runs of a hash leak the same: addresses from `edi` and `esp` -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Pbkdf2.Md.X86 (CmpArgs cmp_ok cmp_rel)
open VG.Proof.Pbkdf2.Stream.X86 (stk After)

/-- `Base` fixes `esp` and `edi`. -/
def baseVal (E : Env) : Reg → BitVec 32 := fun r => if r = .esp then E.sp else E.base.setWidth 32

theorem base_pins {E : Env} {s : State} (B : Base E s) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = baseVal E r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact B.sp
  · exact B.edi

/-- After the hash's first block: the compression function's arguments. -/
def HashMid (E : Env) (g : Geo) (t : State) : Prop :=
  CmpArgs g.H.N g.H.B g.H.so t (E.base.setWidth 32 + BitVec.ofNat 32 sState)
    (E.base.setWidth 32 + BitVec.ofNat 32 sHScr) ∧ t.gpr .esp = E.sp ∧ t.gpr .edi = E.base.setWidth 32

theorem hashPrep_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) :
    WP isa (.block (scr .ebx sState ++ ivStore g.iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (g.H.N + g.qLen) (padBytes g.qLen) ((64 - g.qLen) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 g.H.N))] : List Instr) ++ scr .ebp sHScr)) s
      (HashMid E g) := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have hB := G.hash.B
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have nw := v.scratchFit
  have low := v.low
  have hs := B.scr
  rw [← G.N]
  refine prep_ok G.hash hs (by simp only [sHScr]; omega) fun t eb ea ep gt rd wr _ => ?_
  have tsp : t.gpr .esp = s.gpr .esp := gt _ (by decide) (by decide) (by decide) (by decide)
  have tdi : t.gpr .edi = s.gpr .edi := gt _ (by decide) (by decide) (by decide) (by decide)
  have hsS : sState < E.size := by simp only [sState]; omega
  have hsC : sHScr < E.size := by simp only [sHScr]; omega
  have yNat := Scr.toNat_add hs hsS
  have yW := Scr.wide hs hsS
  have cNat := Scr.toNat_add hs hsC
  have cW := Scr.wide hs hsC
  have stkSub : Region.Sub (stk s) E.stackRegion := by
    simp only [stk, B.sp, Env.stackRegion]; exact below_sub (by decide) (by omega)
  have hstk : (stk s).Disjoint E.scratchRegion := v.scratchStack.symm.sub_left stkSub
  rw [B.edi] at eb ea ep yNat yW cNat cW
  have cargs : CmpArgs g.H.N g.H.B g.H.so t (E.base.setWidth 32 + BitVec.ofNat 32 sState)
      (E.base.setWidth 32 + BitVec.ofNat 32 sHScr) :=
    { ebx := eb
      eax := ea
      ebp := ep
      sp48 := by rw [tsp, B.sp]; omega
      cst := by rw [yW, wr]; exact Scr.covers hs (by rw [hB]; simp only [sState]; omega)
      csc := by rw [cW, wr]; exact Scr.covers hs (by simp only [sHScr]; omega)
      st_sc := by
        rw [yW, cW]
        exact Offset.disjoint E.base (by simp only [sState, sHScr]; rw [hB]; omega) (by rw [hB]; omega) (by omega)
      b_st := by
        rw [stk, tsp, yW]
        exact hstk.sub_right (Offset.sub_base E.base (by rw [hB]; simp only [sState]; omega))
      b_sc := by
        rw [stk, tsp, cW]
        exact hstk.sub_right (Offset.sub_base E.base (by simp only [sHScr]; omega))
      nst := by rw [yNat, hB]; simp only [sState]; omega
      nsc := by rw [cNat]; simp only [sHScr]; omega }
  exact ⟨cargs, tsp.trans B.sp, tdi.trans B.edi⟩

theorem hash_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (dst : Nat) :
    RelCT isa (Both fun (_ : Unit) s => Base E s) (hash g.H g.iv g.qLen dst) fun _ _ => True := by
  have hB := G.hash.B
  unfold Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := fun _ t => HashMid E g t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ B => base_pins B) G.prepCt)
    fun _ s B => hashPrep_ok G v B) ?_
  refine RelCT.seq (both_post (Ψ := fun _ t => t.gpr .esp = E.sp ∧ t.gpr .edi = E.base.setWidth 32)
    ((cmp_rel G.hash.ok.comp (by rw [hB]; decide) (sp := E.sp)
      (fun s s' ⟨_, h, h'⟩ => ⟨h.1, h'.1, h.2.1, h'.2.1⟩)).mono (fun _ _ h => h) fun _ _ h => h)
    fun _ t h => ?_) ?_
  · refine cmp_ok G.hash.ok.comp (by rw [hB]; decide) h.1 fun u au _ => ?_
    exact ⟨(au.cs .esp (by decide)).trans h.2.1, (au.cs .edi (by decide)).trans h.2.2⟩
  · refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ s h r hr => ?_) (G.outCt dst)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

end VG.Proof.Dsa.X86.Generation
