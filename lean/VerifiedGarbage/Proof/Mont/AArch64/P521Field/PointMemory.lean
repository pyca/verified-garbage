module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Spills and streamed loads through stable point pointers. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Weierstrass.AArch64.Mont (ofs_off_sub off_off wordsVal_off)

theorem outside_to_off {p : Addr} {o d n : Nat} {m m' : Mem}
    (h : Outside p (o+d) n m m') (ho : o<2^64) : Outside (off p o) d n m m' := by
  intro x hx
  apply h x
  by_cases hk : ofs p x<o
  · left; omega_arith
  · rw [ofs_off_sub p x o ho] at hx
    have klt : ofs p x<2^64 := (x-p).isLt
    rw [show 2^64-o+ofs p x=(ofs p x-o)+2^64 by omega_arith,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega_arith)] at hx
    omega_arith

theorem point_store_pair {s : State} {po : Addr} {ro : Reg} {cap o so : Nat} {r0 r1 : Reg}
    (ht : PtrW s ro po cap) (hO : o+64≤cap) (ho8 : o%8=0)
    (hs : so+16≤64) (hs8 : so%8=0) (hnd : r0≠r1) :
    WP isa (.block (storesR ro [r0,r1] (o+so))) s fun t =>
      wordsVal t.mem (off po o) so 2=regsVal s [r0,r1] ∧ KeepRegs [] s t ∧
      Outside (off po o) so 16 s.mem t.mem := by
  refine WP.mono (storesR_ok [r0,r1] ht (by simp only [List.length_cons,List.length_nil]; omega_arith)
    (by omega_arith) (by simp [hnd])) fun t ⟨v,k,om⟩ => ?_
  exact ⟨by rw [wordsVal_off]; exact v,k,outside_to_off om (by have he:=ht.enc; omega_arith)⟩

theorem point_spill_load {s : State} {pa po : Addr} {ra ro : Reg} {size cap a o so ao : Nat} {r0 r1 : Reg}
    (ha : Ptr s ra pa size) (ht : PtrW s ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hs : so+16≤64) (hs8 : so%8=0) (hd : ao+16≤72) (hd8 : ao%8=0)
    (hr : ra∉[Reg.x3,.x4]) (hnd : r0≠r1)
    (hread : ∀m,Outside (off po o) so 16 s.mem m →
      word m (off pa a) ao=word s.mem (off pa a) ao ∧ word m (off pa a) (ao+8)=word s.mem (off pa a) (ao+8)) :
    WP isa (.block (storesR ro [r0,r1] (o+so)++loadsR ra [.x3,.x4] (a+ao))) s fun t =>
      wordsVal t.mem (off po o) so 2=regsVal s [r0,r1] ∧
      t.gpr .x3=word s.mem (off pa a) ao ∧ t.gpr .x4=word s.mem (off pa a) (ao+8) ∧
      KeepRegs [.x3,.x4] s t ∧ Outside (off po o) so 16 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (point_store_pair ht hO ho8 hs hs8 hnd) fun u ⟨stored,ku,ou⟩ => ?_
  have hau := ha.of_keepRegs ku (by simp)
  have old := hread u.mem ou
  have hr3 : ra∉[Reg.x3] := by
    intro he
    exact hr (by simpa only [List.mem_cons,List.mem_singleton] using Or.inl (List.mem_singleton.mp he))
  have hl : loadsR ra [.x3,.x4] (a+ao)=([.ldr .x .x3 ra (a+ao)] : List Instr)++[.ldr .x .x4 ra (a+ao+8)] := rfl
  rw [hl,WP.block_append_iff]
  refine WP.mono (ldR_ok hau (d:=a+ao) (by omega_arith) (by omega_arith) .x3) fun v ⟨av,kv,_⟩ => ?_
  refine WP.mono (ldR_ok (hau.of_keeps kv hr3) (d:=a+ao+8) (by omega_arith) (by omega_arith) .x4) fun t ⟨atop,kt,_⟩ => ?_
  refine ⟨by rw [kt.mem,kv.mem]; exact stored,?_,?_,(ku.mono (by sub_regs)).trans
    (((Keeps.regs kv).mono (by sub_regs)).trans ((Keeps.regs kt).mono (by sub_regs))),
    by rw [kt.mem,kv.mem]; exact ou⟩
  · rw [kt.gpr _ (by decide),av]
    simpa only [word,off_off] using old.1
  · rw [atop,kv.mem]
    simpa only [word,off_off,Nat.add_assoc] using old.2

theorem point_spill_load_last {s : State} {pa po : Addr} {ra ro : Reg} {size cap a o : Nat} {r0 r1 : Reg}
    (ha : Ptr s ra pa size) (ht : PtrW s ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0) (hnd : r0≠r1)
    (hread : ∀m,Outside (off po o) 48 16 s.mem m → word m (off pa a) 64=word s.mem (off pa a) 64) :
    WP isa (.block (storesR ro [r0,r1] (o+48)++([.ldr .x .x3 ra (a+64)] : List Instr))) s fun t =>
      wordsVal t.mem (off po o) 48 2=regsVal s [r0,r1] ∧ t.gpr .x3=word s.mem (off pa a) 64 ∧
      KeepRegs [.x3] s t ∧ Outside (off po o) 48 16 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (point_store_pair ht hO ho8 (by decide) (by decide) hnd) fun u ⟨stored,ku,ou⟩ => ?_
  refine WP.mono (ldR_ok (ha.of_keepRegs ku (by simp)) (d:=a+64) (by omega_arith) (by omega_arith) .x3) fun t ⟨atop,kt,_⟩ => ?_
  refine ⟨by rw [kt.mem]; exact stored,?_,(ku.mono (by sub_regs)).trans ((Keeps.regs kt).mono (by sub_regs)),
    by rw [kt.mem]; exact ou⟩
  rw [atop]
  simpa only [word,off_off] using hread u.mem ou

theorem point_store_field {s : State} {po : Addr} {ro : Reg} {cap o : Nat}
    (ht : PtrW s ro po cap) (hO : o+72≤cap) (ho8 : o%8=0) :
    WP isa (.block (storesR ro bRegs o)) s fun t =>
      wordsVal t.mem (off po o) 0 9=regsVal s bRegs ∧ KeepRegs [] s t ∧
      Outside (off po o) 0 72 s.mem t.mem := by
  refine WP.mono (storesR_ok bRegs ht (by simpa only [show bRegs.length=9 from by decide] using hO)
    ho8 (by decide)) fun t ⟨stored,k,outside⟩ => ?_
  simp only [show bRegs.length=9 from by decide] at stored outside
  refine ⟨by rw [wordsVal_off,Nat.add_zero]; exact stored,k,?_⟩
  have h : Outside po (o+0) 72 s.mem t.mem := by simpa only [Nat.add_zero] using outside
  exact outside_to_off h (by have he:=ht.enc; omega_arith)

end VG.Proof.Mont.AArch64.P521Field
