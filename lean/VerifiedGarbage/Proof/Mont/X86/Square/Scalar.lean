module

public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86

def scalar : Instr → Bool
  | .mov .. | .store .. | .alu .. | .shift .. | .mul .. | .bswap .. => true
  | _ => false

theorem scalar_xmm {i : Instr} {s t : State} (h : scalar i = true) (he : exec i s = some t) :
    t.xmm = s.xmm := by
  cases i with
  | mov d src =>
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    rfl
  | store m r =>
    simp only [exec, State.store32] at he
    split at he
    · cases he; rfl
    · cases he
  | alu op d src =>
    cases hr : readSrc s src with
    | none => simp [exec, execAlu, hr] at he
    | some v =>
      cases op <;> cases hc : s.cf <;>
        simp [exec, execAlu, hr, hc] at he <;> cases he <;> rfl
  | shift op d n =>
    simp only [exec, execShift] at he
    split at he
    · cases op <;> simp only [Option.some.injEq] at he <;> cases he <;> rfl
    · cases he
  | mul r => cases he; rfl
  | bswap r => cases he; rfl
  | _ => simp [scalar] at h

theorem scalar_frame {is : List Instr} {s : State} {Q : State → Prop}
    (hi : ∀ i ∈ is, scalar i = true) (h : WP isa (.block is) s Q) :
    WP isa (.block is) s fun t => Q t ∧ t.xmm = s.xmm := by
  induction is generalizing s with
  | nil =>
    exact WP.block_nil ⟨WP.block_nil_iff.mp h, rfl⟩
  | cons i is ih =>
    obtain ⟨s1, he, ht⟩ := WP.block_cons_iff.mp h
    have ex := scalar_xmm (hi i (by simp)) he
    refine WP.block_cons_iff.mpr ⟨s1, he, ?_⟩
    exact WP.mono (ih (fun j hj => hi j (by simp [hj])) ht) fun t ⟨q, eq⟩ => ⟨q, eq.trans ex⟩

theorem wp_cmpCF {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, VG.X86.Wp.Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  VG.X86.Wp.cons (s' := arithFlags s (s.gpr d-v) (decide ((s.gpr d).toNat<v.toNat)) (subOverflow (s.gpr d) v (s.gpr d-v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end VG.Proof.Mont.X86.Square
