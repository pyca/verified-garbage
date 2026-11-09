module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
import VerifiedGarbage.Proof.Framework.Block

/-! The paired load/carry schedule, preserving the pointer and unread limbs. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def pairRegs : List (Reg × Reg) → List Reg
  | [] => []
  | (a,b)::ps => a::b::pairRegs ps

def linearAddPairs (rn : Reg) : List (Reg × Reg) → Nat → List Instr
  | [], _ => []
  | (a,b)::ps, o => linearAddPair rn a b o++linearAddPairs rn ps (o+16)

theorem linear_add_pairs_ok {size : Nat} {rn : Reg} :
    ∀ (ps : List (Reg × Reg)) {s : State} {p : Addr} {b : Nat},
    Ptr s rn p size → b+8*(pairRegs ps).length≤size → b%8=0 →
    (pairRegs ps).Nodup → rn≠.x3 → rn≠.x4 →
    (∀ r∈pairRegs ps, r∉[Reg.x3,.x4,rn]) →
    WP isa (.block (linearAddPairs rn ps b)) s fun t =>
      regsVal t (pairRegs ps)+2^(64*(pairRegs ps).length)*t.c.toNat=
        regsVal s (pairRegs ps)+wordsVal s.mem p b (pairRegs ps).length+s.c.toNat ∧
      Keeps (.x3::.x4::pairRegs ps) s t
  | [], s, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [pairRegs,regsVal,wordsVal],
      fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | (a,d)::ps, s, p, b, hp, hb, hb8, hn, hr3, hr4, hf => by
    have ha := hf a (by simp [pairRegs])
    have hd := hf d (by simp [pairRegs])
    have hn' := List.nodup_cons.mp hn
    have hn'' := List.nodup_cons.mp hn'.2
    have had : a≠d := fun e => hn'.1 (by simp [←e])
    have ha34 : a∉[Reg.x3,.x4] := fun e => ha (by simp_all)
    have hd34 : d∉[Reg.x3,.x4] := fun e => hd (by simp_all)
    rw [linearAddPairs,WP.block_append_iff]
    refine WP.mono (linear_add_pair_value hp (by simp only [pairRegs,List.length_cons] at hb; omega_arith)
      hb8 hr4 had ha34 hd34) fun u ⟨e0,k0⟩ => ?_
    have hpu := hp.of_keeps k0 (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hr3,hr4,fun e => ha (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr e.symm))),fun e => hd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr e.symm)))⟩)
    refine WP.mono (linear_add_pairs_ok ps hpu
      (by simp only [pairRegs,List.length_cons] at hb; omega_arith)
      (by omega_arith) hn''.2 hr3 hr4 (fun r h => hf r (by simp [pairRegs,h])))
      fun t ⟨e1,k1⟩ => ?_
    have hta : t.gpr a=u.gpr a := k1.gpr a (by
      simp only [List.mem_cons,not_or]; exact ⟨(by simpa using ha34 : a≠.x3 ∧ a≠.x4).1,(by simpa using ha34 : a≠.x3 ∧ a≠.x4).2,fun h => hn'.1 (by simp [h])⟩)
    have htd : t.gpr d=u.gpr d := k1.gpr d (by
      simp only [List.mem_cons,not_or]; exact ⟨(by simpa using hd34 : d≠.x3 ∧ d≠.x4).1,(by simpa using hd34 : d≠.x3 ∧ d≠.x4).2,hn''.1⟩)
    have htail : regsVal u (pairRegs ps)=regsVal s (pairRegs ps) := regsVal_congr fun r h =>
      k0.gpr r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        have hfr := hf r (List.mem_cons_of_mem a (List.mem_cons_of_mem d h))
        exact ⟨by intro e; exact hfr (by simp [e]),by intro e; exact hfr (by simp [e]),
          fun e => hn'.1 (List.mem_cons_of_mem d (e ▸ h)),fun e => hn''.1 (e ▸ h)⟩)
    rw [htail,k0.mem] at e1
    refine ⟨?_,(k0.mono (by
      intro r h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [pairRegs])).trans (k1.mono (by
      intro r h
      simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · simp [pairRegs]
      · simp [pairRegs]
      · change r ∈ .x3::.x4::a::d::pairRegs ps
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))))⟩
    have hpw : 2^(64*(pairRegs ((a,d)::ps)).length)=2^128*2^(64*(pairRegs ps).length) := by
      simp only [pairRegs,List.length_cons,pow64_succ]
      omega_arith
    rw [hpw]
    simp only [pairRegs,regsVal,wordsVal,List.length_cons,hta,htd,Nat.add_assoc,
      Nat.add_zero,Nat.mul_zero,Nat.mul_add,Nat.mul_assoc,Nat.reduceAdd] at e0 ⊢
    omega_using [e0,e1]

end VG.Proof.Mont.AArch64.P521Field
