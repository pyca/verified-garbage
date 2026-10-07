import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Closed

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRcx_ok (s : State) :
    WP isa (.block [.alu32 .xor .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rcx=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu32,readSrc32,Option.bind_some,
    State.setReg32,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,rfl,fun r hr => ?_,rfl,rfl,rfl⟩
  · simp only [RegUpd.gpr_setReg_self,BitVec.xor_self]; rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr,RegUpd.gpr_arithFlags]

theorem rowCore_ok (rs : List Reg) {s : State} {B : Addr} {Z e i : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e)
    (hZ : e+8*(i+rs.length) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx)
    (hv : value s rs<2^(64*(rs.length-1))) :
    WP isa (.block (AdxTri8.rowCore i rs)) s fun t =>
      value t rs=value s rs+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) (rs.length-1) ∧
      Keeps (([.rdx,.rcx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  have len : 0<rs.length := List.length_pos_iff.mpr hn
  have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*i)) (by omega : e+8*i+8≤Z)
  unfold AdxTri8.rowCore
  rw [WP.block_append_iff]
  rw [show ([.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor .rcx (.reg .rcx)] : List Instr)=
    [.mov .rdx (.mem (at_ .rbp (8*i)))] ++ [.alu32 .xor .rcx (.reg .rcx)] from rfl,WP.block_append_iff]
  refine WP.mono (movMem_ok s hm) fun a ⟨pa,_,_,ka⟩ => ?_
  refine WP.mono (xorRcx_ok a) fun b ⟨zb,cb,ob,kb⟩ => ?_
  have kab := ka.trans kb
  have vb : value b rs=value s rs := value_congr fun r hr =>
    kab.gpr (by have h := hrs r hr; simp [h.1.2.2.1,h.1.2.2.2])
  refine WP.mono (chain_closed rs (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans hp) zb
    (by omega) hn hd hrs cb ob (by rw [vb]; exact hv)) fun t ⟨eq,kt⟩ => ?_
  rw [vb,kab.2.1,kb.gpr (by decide),pa] at eq
  exact ⟨eq,(kab.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxTri8
