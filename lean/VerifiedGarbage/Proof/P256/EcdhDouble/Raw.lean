module

public import VerifiedGarbage.Impl.P256.EcdhDouble
import VerifiedGarbage.Proof.P256.EcdhDouble.WeakField
public import VerifiedGarbage.Proof.P256.EcdhDouble.MacroField
public import VerifiedGarbage.Proof.P256.EcdhDouble.Arithmetic
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.AArch64.Inline

@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M)

def ops1 : List FOp := [.mul 800 576 576,.mul 832 544 544,.sub 896 512 800]
def ops2 : List FOp := [.add 864 544 576,.mul 928 512 832,.mul 960 896 896,.mul 864 864 864]
def ops3 : List FOp := [.sub 864 864 800,.sub 576 864 832]
def ops4 : List FOp := [.mul 896 960 896,.mul 800 832 832]
def writes : List Nat := [512,544,576,800,832,864,896,928,960]
def result {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) : Nat→F :=
  let e := runOps ops1 E
  let e := Function.update e 896 ((e 512+e 800)*e 896)
  let e := runOps ops2 e
  let e := Function.update e 960 (12*e 928-9*e 960)
  let e := runOps ops3 e
  let e := Function.update e 512 (4*e 928-e 960)
  let e := runOps ops4 e
  Function.update e 544 (3*e 896-8*e 800)

theorem result_xyz {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) :
    (result E 512,result E 544,result E 576)=values (E 512) (E 544) (E 576) := by
  simp [result,ops1,ops2,ops3,ops4,runOps,FOp.run,values]

theorem opKeep_prog {base : Addr} {o : Nat} {s t : State} (hk : OpKeep M base o s t) :
    ProgKeep M base [o] s t :=
  ⟨hk.gpr,hk.rd,hk.wr,hk.sp,fun x hx ht => hk.mem x (hx o (by simp)) ht⟩

theorem prog_trans {base : Addr} {s t u : State} {W : List Nat}
    (h1 : ProgKeep M base W s t) (h2 : ProgKeep M base W t u) : ProgKeep M base W s u :=
  ⟨fun r hr => (h2.gpr r hr).trans (h1.gpr r hr),h2.rd.trans h1.rd,h2.wr.trans h1.wr,
   h2.sp.trans h1.sp,fun x hx ht => (h2.mem x hx ht).trans (h1.mem x hx ht)⟩

theorem result_unch {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) {x : Nat}
    (hx : x∉writes) : result E x=E x := by
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
  simp [result,ops1,ops2,ops3,ops4,runOps,FOp.run,
    hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.2]

/-- The slots the field operations name lie among the doubling's writes. -/
theorem slots_of {Sl : Nat → Prop} (hw : ∀ x∈writes,Sl x) {ops : List FOp}
    (h : ∀ op∈ops,∀ x∈op.out::op.ins,x∈writes) : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x :=
  fun op hop x hx => hw x (h op hop x hx)

/-- The raw doubling from the accumulator `R` alone: every written slot ends valid. -/
theorem rawR_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hw : ∀ x∈writes,Sl x)
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {base : Addr} {s : State} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl [512,544,576] E s) :
    WP isa (.block Impl.P256.EcdhDouble.raw) s fun t =>
      ProgKeep M base writes s t ∧ Inv M base 8192 C.p Sl writes (result E) t := by
  have cut : Impl.P256.EcdhDouble.raw = ops1.flatMap Impl.P256.VerifySparse.op ++ weakMulCode ++
    ops2.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear129 960 928 960 ++
    ops3.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear41 512 928 960 ++
    ops4.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear38 544 896 800 := by
      simp only [Impl.P256.EcdhDouble.raw,ops1,ops2,ops3,ops4,weakMulCode,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  have sw (x : Nat) (hx : x∈writes := by decide) : Sl x := hw x hx
  rw [cut]
  simp only [List.append_assoc]
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops1 hi
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s1 ⟨k1,i1⟩ => ?_
  apply WP.block_append
  refine WP.mono (weakMul_ok layout aligned (sw 864) (sw 896) hm i1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun s2 ⟨k2,i2⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops2 i2
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s3 ⟨k3,i3⟩ => ?_
  apply WP.block_append
  refine WP.mono (linearField_ok layout h129 (sw 960) i3 (by decide +kernel) (by decide +kernel))
    fun s4 ⟨k4,i4⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops3 i4
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s5 ⟨k5,i5⟩ => ?_
  apply WP.block_append
  refine WP.mono (linear41Field_ok layout (sw 512) i5 (by decide +kernel) (by decide +kernel))
    fun s6 ⟨k6,i6⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops4 i6
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s7 ⟨k7,i7⟩ => ?_
  refine WP.mono (linearField_ok layout h38 (sw 544) i7 (by decide +kernel) (by decide +kernel))
    fun t ⟨k8,i8⟩ => ?_
  refine ⟨?_,?_⟩
  · exact prog_trans (prog_trans (prog_trans (prog_trans (prog_trans (prog_trans (prog_trans
      (k1.mono (by decide +kernel)) (k2.mono (by decide +kernel))) (k3.mono (by decide +kernel)))
      ((opKeep_prog k4).mono (by decide +kernel))) (k5.mono (by decide +kernel)))
      ((opKeep_prog k6).mono (by decide +kernel))) (k7.mono (by decide +kernel)))
      ((opKeep_prog k8).mono (by decide +kernel))
  · exact i8.sub (by decide +kernel)

/-- The raw doubling on any live slots holding `R`: it keeps those it does not write. -/
theorem raw_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hw : ∀ x∈writes,Sl x)
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {live : List Nat} (hR : ∀ x∈[512,544,576],x∈live)
    {base : Addr} {s : State} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl live E s) :
    WP isa (.block Impl.P256.EcdhDouble.raw) s fun t =>
      ProgKeep M base writes s t ∧ Inv M base 8192 C.p Sl live (result E) t := by
  refine WP.mono (rawR_ok layout aligned hw h129 h38 hm (hi.sub hR)) fun t ⟨hk,it⟩ => ⟨hk,?_⟩
  have keep (x : Nat) (hx : x∈live) (hn : x∉writes) :
      wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
    have hb := layout.le x (hi.sl x hx)
    refine hk.unch.wordsVal (fun w hw' => ?_) (by omega)
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw'
    rcases hw' with ⟨y,hy,rfl⟩ | rfl
    · exact layout.apart x y (hi.sl x hx) (hw y hy) (fun he => hn (he ▸ hy))
    · exact layout.tmp x (hi.sl x hx)
  refine ⟨it.scr,it.mod,hi.sl,fun x hx => ?_,fun x hx => ?_⟩
  · by_cases hn : x∈writes
    · exact it.lt x hn
    · rw [keep x hx hn]; exact hi.lt x hx
  · by_cases hn : x∈writes
    · exact it.val x hn
    · rw [keep x hx hn,hi.val x hx,result_unch E hn]
end VG.Proof.P256.EcdhDouble
