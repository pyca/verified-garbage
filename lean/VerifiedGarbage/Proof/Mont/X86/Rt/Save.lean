module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Stages
import VerifiedGarbage.Proof.Framework.Omega

/-! # Saving and restoring the callee-saved registers

`save`: `edi` at the function's range `S`, and `ebx`, `esi`, `ebp`, `edi`
in its words 36 to 51 (`save_ok`); `restoreRegs`: them back (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The saved words hold `g` of the callee-saved registers. -/
def SavedAt (m : Mem) (W : Addr) (S : Nat) (g : Reg → BitVec 32) : Prop :=
  m.readW (off W (S + 36)) 32 = g .ebx ∧ m.readW (off W (S + 40)) 32 = g .esi ∧
    m.readW (off W (S + 44)) 32 = g .ebp ∧ m.readW (off W (S + 48)) 32 = g .edi

theorem SavedAt.of_outs {m m' : Mem} {W : Addr} {S : Nat} {g : Reg → BitVec 32} {rs : List (Nat × Nat)}
    (h : SavedAt m W S g) (O : Outs W rs m m') (hrs : ∀ r ∈ rs, S + 52 ≤ r.1 ∨ r.1 + r.2 ≤ S + 36)
    (hS : S + 52 ≤ 2 ^ 32) : SavedAt m' W S g := by
  have k : ∀ d, S + 36 ≤ d → d + 4 ≤ S + 52 → m'.readW (off W d) 32 = m.readW (off W d) 32 := by
    intro d h₁ h₂
    exact Mem.readW_congr fun i hi => O _ fun r hr => by
      rw [show off W d + BitVec.ofNat 64 i = off W (d + i) by simp only [off, Offset.add_add],
        ofs_off0 W (by omega)]
      have := hrs r hr
      have : i < 4 := hi
      omega
  exact ⟨(k _ (by omega) (by omega)).trans h.1, (k _ (by omega) (by omega)).trans h.2.1,
    (k _ (by omega) (by omega)).trans h.2.2.1, (k _ (by omega) (by omega)).trans h.2.2.2⟩

theorem save_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {S : Nat} (hA0 : (A 0).toNat = W.toNat) (hA5 : (A 5).toNat = S) (hS : S + 52 ≤ L) :
    WP isa (.block save) s fun t =>
      PtrAt t W .edi S ∧ SavedAt t.mem W S s.gpr ∧ Outside W (S + 36) 16 s.mem t.mem ∧
      Keeps [.eax, .edx, .edi] s t := by
  have hn := hw.nowrap
  simp only [save, saveSlots, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (ptr_ok ha (r := .eax) (t := .edx) (i := 5) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, _, m₁, K₁⟩ => ?_)
  have hw₁ := hw.of_keeps K₁
  have eax₁ : PtrAt s₁ W .eax S := by rw [PtrAt, e₁, BitVec.toNat_add, hA0, hA5]
  have st : ∀ (t : State) (d : Nat), t.gpr .eax = s₁.gpr .eax → t.wr = s₁.wr → d + 4 ≤ 16 →
      t.ea (at_ .eax (36 + d)) = off W (S + 36 + d) ∧ InRegions t.wr (off W (S + 36 + d)) 4 := by
    intro t d he hwr hd
    have hwt : Ws t W L := hw₁.of_wr hwr
    have ep : PtrAt t W .eax S := by rw [PtrAt, he]; exact eax₁
    refine ⟨by rw [ea_ptr hwt ep (by omega_using [hS, hd])]; congr 1; omega_using [],
      ws_write hwt (by omega_using [hS, hd])⟩
  obtain ⟨a₁, w₁⟩ := st s₁ 0 rfl rfl (by decide)
  refine wp_storeS a₁ w₁ fun s₂ m₂ => ?_
  obtain ⟨a₂, w₂⟩ := st s₂ 4 (by rw [m₂.gpr]) m₂.wr (by decide)
  refine wp_storeS a₂ w₂ fun s₃ m₃ => ?_
  obtain ⟨a₃, w₃⟩ := st s₃ 8 (by rw [m₃.gpr, m₂.gpr]) (by rw [m₃.wr, m₂.wr]) (by decide)
  refine wp_storeS a₃ w₃ fun s₄ m₄ => ?_
  obtain ⟨a₄, w₄⟩ := st s₄ 12 (by rw [m₄.gpr, m₃.gpr, m₂.gpr]) (by rw [m₄.wr, m₃.wr, m₂.wr]) (by decide)
  refine wp_storeS a₄ w₄ fun s₅ m₅ => wp_movS rfl fun s₆ u₆ _ => WP.block_nil ?_
  have g₄ : s₄.gpr = s₁.gpr := by rw [m₄.gpr, m₃.gpr, m₂.gpr]
  have gs : ∀ r, r ≠ .eax → r ≠ .edx → s₁.gpr r = s.gpr r := fun r h₁ h₂ => K₁.1 r (by simp [h₁, h₂])
  have mem₅ : s₅.mem = ((((s.mem.writeW (off W (S + 36 + 0)) (s.gpr .ebx)).writeW (off W (S + 36 + 4))
      (s.gpr .esi)).writeW (off W (S + 36 + 8)) (s.gpr .ebp)).writeW (off W (S + 36 + 12)) (s.gpr .edi)) := by
    rw [m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁, g₄, m₃.gpr, m₂.gpr, gs _ (by decide) (by decide),
      gs _ (by decide) (by decide), gs _ (by decide) (by decide), gs _ (by decide) (by decide)]
  simp only [Nat.add_zero] at mem₅
  refine ⟨?_, ?_, ?_, ((K₁.mono (by decide)).widen (m₂.keeps [])).widen (m₃.keeps []) |>.widen (m₄.keeps [])
    |>.widen (m₅.keeps []) |>.widen u₆.keeps⟩
  · rw [PtrAt, u₆.gpr, m₅.gpr, g₄]; exact eax₁
  · rw [u₆.mem, mem₅]
    have r : ∀ (m : Mem) (o d : Nat) (v : BitVec 32), d + 4 ≤ o ∨ o + 4 ≤ d → o + 4 ≤ L → d + 4 ≤ L →
        (m.writeW (off W o) v).readW (off W d) 32 = m.readW (off W d) 32 := fun m o d v hsep ho hd =>
      Mem.readW_writeW_sep (Offset.sep W hsep (by omega) (by omega)) (by decide)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]),
        r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]),
        r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]), Mem.readW_writeW_self32]
    · rw [r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]),
        r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]), Mem.readW_writeW_self32]
    · rw [r _ _ _ _ (by omega_using []) (by omega_using [hS]) (by omega_using [hS]), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · rw [u₆.mem, mem₅]
    have o : ∀ (m : Mem) (d : Nat) (v : BitVec 32), S + 36 ≤ d → d + 4 ≤ S + 52 →
        Outside W (S + 36) 16 m (m.writeW (off W d) v) := fun m d v h₁ h₂ =>
      ((writeW32_outside m W v (by omega)).mono h₁ (by omega))
    exact (((o _ _ _ (by omega_using []) (by omega_using [])).trans (o _ _ _ (by omega_using []) (by omega_using []))).trans
      (o _ _ _ (by omega_using []) (by omega_using []))).trans (o _ _ _ (by omega_using []) (by omega_using []))

theorem restore_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {S : Nat} (hA0 : (A 0).toNat = W.toNat) (hA5 : (A 5).toNat = S) (hS : S + 52 ≤ L)
    {g : Reg → BitVec 32} (hs : SavedAt s.mem W S g) :
    WP isa (.block restoreRegs) s fun t =>
      t.gpr .ebx = g .ebx ∧ t.gpr .esi = g .esi ∧ t.gpr .ebp = g .ebp ∧ t.gpr .edi = g .edi ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] s t := by
  have hn := hw.nowrap
  simp only [restoreRegs, saveSlots, List.map_cons, List.map_nil]
  refine WP.block_append (WP.mono (ptr_ok ha (r := .edi) (t := .eax) (i := 5) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, _, m₁, K₁⟩ => ?_)
  have hw₁ := hw.of_keeps K₁
  have edi₁ : PtrAt s₁ W .edi S := by rw [PtrAt, e₁, BitVec.toNat_add, hA0, hA5]
  rw [← m₁] at hs
  refine wp_movS (readSrc_ptr hw₁ edi₁ (d := 36) (by omega_using [hS])) fun s₂ u₂ _ => ?_
  have edi₂ : PtrAt s₂ W .edi S := by rw [PtrAt, u₂.other _ (by decide)]; exact edi₁
  have hw₂ := hw₁.of_keeps u₂.keeps
  refine wp_movS (readSrc_ptr hw₂ edi₂ (d := 40) (by omega_using [hS])) fun s₃ u₃ _ => ?_
  have edi₃ : PtrAt s₃ W .edi S := by rw [PtrAt, u₃.other _ (by decide)]; exact edi₂
  have hw₃ := hw₂.of_keeps u₃.keeps
  refine wp_movS (readSrc_ptr hw₃ edi₃ (d := 44) (by omega_using [hS])) fun s₄ u₄ _ => ?_
  have edi₄ : PtrAt s₄ W .edi S := by rw [PtrAt, u₄.other _ (by decide)]; exact edi₃
  have hw₄ := hw₃.of_keeps u₄.keeps
  refine wp_movS (readSrc_ptr hw₄ edi₄ (d := 48) (by omega_using [hS])) fun s₅ u₅ _ => WP.block_nil ?_
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  refine ⟨?_, ?_, ?_, ?_, by rw [u₅.mem, m₄, m₁], ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; exact hs.1
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem]; exact hs.2.1
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem]; exact hs.2.2.1
  · rw [u₅.gpr, m₄]; exact hs.2.2.2
  · exact ((((K₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps

end VG.Proof.Mont.X86.Rt
