module

public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! Two-word spills and streamed input loads, independent of arithmetic. -/

-- separate module: the multiplication's memory phase is shared by each pair of rows
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem _root_.VG.Proof.Mont.AArch64.Ptr.of_keepRegs {rs : List Reg} {s t : State} {r : Reg} {base : Addr} {size : Nat}
    (h : Ptr s r base size) (k : KeepRegs rs s t) (hr : r∉rs) : Ptr t r base size :=
  ⟨(k.gpr r hr).trans h.reg,by rw [k.rd,k.wr]; exact h.ld,h.enc⟩

def spillPair (r0 r1 : Reg) (d : Nat) : List Instr := storesR .x27 [r0,r1] d

def loadPair (d : Nat) : List Instr := loadsR .x1 [.x3,.x4] d

/-- The spill may change only its sixteen scratch bytes. The input-load
premise states explicitly that these bytes do not contain the unread input. -/
theorem spill_load_ok {s : State} {pa pt : Addr} {so ao : Nat} {r0 r1 : Reg}
    (ha : Ptr s .x1 pa 72) (ht : PtrW s .x27 pt 64)
    (hs : so+16≤64) (hs8 : so%8=0) (hd : ao+16≤72) (hd8 : ao%8=0)
    (hnd : r0≠r1)
    (hread : ∀m,Outside pt so 16 s.mem m →
      word m pa ao=word s.mem pa ao ∧ word m pa (ao+8)=word s.mem pa (ao+8)) :
    WP isa (.block (spillPair r0 r1 so ++ loadPair ao)) s fun t =>
      wordsVal t.mem pt so 2 = regsVal s [r0,r1] ∧
      t.gpr .x3=word s.mem pa ao ∧ t.gpr .x4=word s.mem pa (ao+8) ∧
      KeepRegs [.x3,.x4] s t ∧ Outside pt so 16 s.mem t.mem := by
  rw [spillPair,WP.block_append_iff]
  refine WP.mono (storesR_ok [r0,r1] ht hs hs8 (by simp [hnd])) fun u ⟨stored,ku,ou⟩ => ?_
  have hau := ha.of_keepRegs ku (by decide)
  have old := hread u.mem ou
  have hl : loadPair ao = ([.ldr .x .x3 .x1 ao] : List Instr) ++ [.ldr .x .x4 .x1 (ao+8)] := rfl
  rw [hl,WP.block_append_iff]
  refine WP.mono (ldR_ok hau (d:=ao) (by omega_arith) hd8 .x3) fun v ⟨av,kv,_⟩ => ?_
  refine WP.mono (ldR_ok (hau.of_keeps kv (by decide)) (d:=ao+8)
    (by omega_arith) (by omega_arith) .x4) fun t ⟨a_t,kt,_⟩ => ?_
  refine ⟨?_,?_,?_,(ku.mono (by sub_regs)).trans
    (((VG.Proof.Mont.AArch64.Keeps.regs kv).mono (by sub_regs)).trans ((VG.Proof.Mont.AArch64.Keeps.regs kt).mono (by sub_regs))),?_⟩
  · rw [kt.mem,kv.mem]; exact stored
  · rw [kt.gpr _ (by decide),av]; exact old.1
  · rw [a_t,kv.mem]; exact old.2
  · rw [kt.mem,kv.mem]; exact ou

/-- The last spill is followed by only the final input limb's load. -/
theorem spill_load_last_ok {s : State} {pa pt : Addr} {r0 r1 : Reg}
    (ha : Ptr s .x1 pa 72) (ht : PtrW s .x27 pt 64) (hnd : r0≠r1)
    (hread : ∀m,Outside pt 48 16 s.mem m → word m pa 64=word s.mem pa 64) :
    WP isa (.block (spillPair r0 r1 48++([.ldr .x .x3 .x1 64] : List Instr))) s fun t =>
      wordsVal t.mem pt 48 2=regsVal s [r0,r1] ∧ t.gpr .x3=word s.mem pa 64 ∧
      KeepRegs [.x3] s t ∧ Outside pt 48 16 s.mem t.mem := by
  rw [spillPair,WP.block_append_iff]
  refine WP.mono (storesR_ok [r0,r1] ht (by simp only [List.length_cons,List.length_nil]; decide) (by decide) (by simp [hnd]))
    fun u ⟨stored,ku,ou⟩ => ?_
  refine WP.mono (ldR_ok (ha.of_keepRegs ku (by decide)) (d:=64)
    (by decide) (by decide) .x3) fun t ⟨a,kt,_⟩ => ?_
  exact ⟨by rw [kt.mem]; exact stored,by rw [a,hread u.mem ou],
    (ku.mono (by sub_regs)).trans ((VG.Proof.Mont.AArch64.Keeps.regs kt).mono (by sub_regs)),
    by rw [kt.mem]; exact ou⟩

end VG.Proof.Mont.AArch64.P521Field
