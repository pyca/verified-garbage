module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Words
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Zeros at an output (x86)

`zeroOut d` writes `p_len` zeros at the pointer in the state's word at `d`,
one byte at a time (`zeroOut_ok`), changing only `eax`, `ecx` and `edx`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch

/-- A byte of a store of one byte. -/
theorem byte_write {m : Mem} {a x : Addr} {v : BitVec 8} : (m.writeW a v) x = if x = a then v else m x := by
  have e : (x - a).toNat < 8 / 8 ↔ x = a := by
    rw [show 8 / 8 = 1 from rfl, Nat.lt_one_iff, ← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    constructor
    · intro h; rw [← BitVec.sub_add_cancel x a, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  simp only [Mem.writeW, Mem.write, e]
  split
  · next h => subst h; simp
  · rfl

/-- `mov byte [m], r`. -/
theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {r : Reg8} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem Upd.keeps {s t : State} {d : Reg} {v : BitVec 32} (h : Upd s t d v) : Keeps [d] s t :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ List.mem_singleton_self _), h.rd, h.wr⟩

theorem Mupd.keeps {s t : State} {m : Mem} (h : Mupd s t m) (rs : List Reg) : Keeps rs s t :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

/-- The output after `k` of its `n` bytes are zeroed. -/
structure ZInv (s₀ : State) (P : BitVec 32) (n k : Nat) (t : State) : Prop where
  edx : t.gpr .edx = P + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 (n - k)
  eax : t.gpr .eax = 0
  frame : Frame [⟨P.setWidth 64, n⟩] s₀.mem t.mem
  zero : ∀ i < k, t.mem (P.setWidth 64 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .edx] s₀ t

theorem zeroStep_ok {s₀ t : State} {P : BitVec 32} {n k : Nat} (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s₀.wr)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32) (hk : k < n) (I : ZInv s₀ P n k t) :
    WP isa (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZInv s₀ P n (k + 1) u ∧ u.zf = some (decide (n - (k + 1) = 0)) := by
  have hp : t.ea (at_ .edx 0) = P.setWidth 64 + BitVec.ofNat 64 k := by
    show (t.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega)
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    ⟨_, by rw [I.keeps.2.2]; exact hR, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) hik)]
      exact I.zero i (by omega)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- `p_len` zeros at the pointer `P` in the state's word at `d`. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {d n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S d) 4) (hl : InRegions (s.rd ++ s.wr) (addr S lenOff) 4)
    (hP : s.mem.readW (addr S d) 32 = P) (hn : s.mem.readW (addr S lenOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa (zeroOut d) s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
  have m₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZInv s P n 0 t₃ := ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hP, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, hn, Nat.sub_zero],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), k₃⟩
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = n - k ∧ k < n ∧ ZInv s P n k u)
    (fun j u hu => ?_) _ t₃ ⟨0, rfl, h0, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hR hb hn32 hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : n - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.frame, ?_, J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega,
      k + 1, rfl, by omega, J⟩

end VG.Proof.Ffdh.X86.KeySearch
