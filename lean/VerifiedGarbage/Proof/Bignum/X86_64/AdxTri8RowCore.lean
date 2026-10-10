import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chain

/-! ## AdxTri8Closed -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

private theorem mac_bound {R Q X U V : Nat} (hx : X<R) (hu : U<Q) (hv : V<Q) : V+X*U<R*Q := by
  have h : X*U ≤ (R-1)*(Q-1) := Nat.mul_le_mul (by omega) (by omega)
  have e : (Q-1)+(R-1)*(Q-1)+R=R*Q := by
    calc
      _ = ((R-1)+1)*(Q-1)+R := by rw [Nat.add_mul,Nat.one_mul]; omega
      _ = R*(Q-1)+R := by rw [Nat.sub_add_cancel (by omega : 1≤R)]
      _ = R*((Q-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = R*Q := by rw [Nat.sub_add_cancel (by omega : 1≤Q)]
  omega

private theorem no_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega)
    omega
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

/-- The top accumulator word is reserved for the product carry. A zero top
word makes it impossible to lose a carry when the next triangular row starts. -/
theorem chain_closed (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e) (hz : s.gpr .rax=0)
    (hZ : e+8*(k+(rs.length-1)) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx)
    (hc : s.cf=some false) (ho : s.of=some false)
    (hv : value s rs<2^(64*(rs.length-1))) :
    WP isa (.block (AdxTri8.chain k .rbx .rax .rax rs)) s fun t =>
      value t rs=value s rs+(s.gpr .rdx).toNat*wv s.mem B (e+8*k) (rs.length-1) ∧
      Keeps (([.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  refine WP.mono (chain_ok rs hs hp hv hZ hn hd (by unfold Safe; decide) (by unfold Safe; decide) (by decide)
    (by decide) (by decide) (fun r h => let q := hrs r h; ⟨q.1,q.2.2.1,q.2.1,q.2.1⟩) hc ho) fun t ⟨c,o,_,_,eq,kt⟩ => ?_
  rw [hz] at eq
  simp only [Bool.toNat_false,show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero] at eq
  have bound := mac_bound (s.gpr .rdx).isLt (wv_lt s.mem B (e+8*k) (rs.length-1)) hv
  rw [← Nat.pow_add,show 64+64*(rs.length-1)=64*rs.length by have := List.length_pos_iff.mpr hn; omega] at bound
  exact ⟨no_carry eq bound,kt.mono (by
    intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with (h|h|h)|h <;> simp [h])⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8RowCore -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [.rax] s t := by
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
      Keeps (([.rdx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  have len : 0<rs.length := List.length_pos_iff.mpr hn
  have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*i)) (by omega : e+8*i+8≤Z)
  unfold AdxTri8.rowCore
  rw [WP.block_append_iff]
  rw [show ([.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor .rax (.reg .rax)] : List Instr)=
    [.mov .rdx (.mem (at_ .rbp (8*i)))] ++ [.alu32 .xor .rax (.reg .rax)] from rfl,WP.block_append_iff]
  refine WP.mono (movMem_ok s hm) fun a ⟨pa,_,_,ka⟩ => ?_
  refine WP.mono (xorRax_ok a) fun b ⟨zb,cb,ob,kb⟩ => ?_
  have kab := ka.trans kb
  have vb : value b rs=value s rs := value_congr fun r hr =>
    kab.gpr (by have h := hrs r hr; simp [h.1.2.2.1,h.2.1])
  refine WP.mono (chain_closed rs (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans hp) zb
    (by omega) hn hd hrs cb ob (by rw [vb]; exact hv)) fun t ⟨eq,kt⟩ => ?_
  rw [vb,kab.2.1,kb.gpr (by decide),pa] at eq
  exact ⟨eq,(kab.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end
