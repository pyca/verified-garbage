module

public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.Proof.Ed25519.X86.CopyWords
public import VerifiedGarbage.Proof.Ed25519.X86.Field

/-! ### `Ed25519.X86.PointTable`, which this module and modules that import it used -/

section

/-! Saving and loading four consecutive field coordinates. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def tablePoint (m : Mem) (x : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨F m x o, F m x (o + 32), F m x (o + 64), F m x (o + 96)⟩

theorem fields_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, wd m' x (o + 4 * k) = wd m x (a + 4 * k))
    (j : Nat) (hj : j < 4) : F m' x (o + 32 * j) = F m x (a + 32 * j) := by
  apply congrArg VG.Proof.X25519.toFe
  apply num_congr
  intro k hk
  have hv := h (8 * j + k) (by omega_using [hj, hk])
  have he : o + 32 * j + 4 * k = o + 4 * (8 * j + k) := by omega_using []
  have he' : a + 32 * j + 4 * k = a + 4 * (8 * j + k) := by omega_using []
  exact congrArg BitVec.toNat (he.symm ▸ he'.symm ▸ hv)

theorem point_mk_congr {a b c d a' b' c' d' : Spec.X25519.Fe}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    Spec.Ed25519.Point.mk a b c d = Spec.Ed25519.Point.mk a' b' c' d' := by
  cases ha; cases hb; cases hc; cases hd; rfl

theorem table_point_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, wd m' x (o + 4 * k) = wd m x (a + 4 * k)) :
    tablePoint m' x o = tablePoint m x a := by
  have h0 := fields_of_words h 0 (by decide)
  have h1 := fields_of_words h 1 (by decide)
  have h2 := fields_of_words h 2 (by decide)
  have h3 := fields_of_words h 3 (by decide)
  exact point_mk_congr h0 h1 h2 h3

theorem pointToTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      CopyKeep x o 128 s t ∧ tablePoint t.mem x o = point (env s.mem x) 0 1 2 3 := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edi .edx (by decide) (by decide) 0 o 64 0 32
    hb hp (by decide) (by omega_using [ho]) (Or.inl hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  refine ⟨hk, ?_⟩
  exact table_point_of_words hv

theorem pointFromTable_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      CopyKeep x 64 128 s t ∧ point (env t.mem x) 0 1 2 3 = tablePoint s.mem x o := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 64 32
    hp hb (by omega_using [ho]) (by decide) (Or.inr hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  exact ⟨hk, table_point_of_words hv⟩

theorem table_env {x : BitVec 32} {o n : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [sub x o n] m m')
    (ho : 768 ≤ o) (hn : o + n ≤ 8192) : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx hn (by simp only [offset]; omega_using [])
    (Or.inl (by simp only [offset]; omega_using [ho]))

theorem tablePoint_frame {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [sub x o n] m m')
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hsep : a + 128 ≤ o ∨ o + n ≤ a) :
    tablePoint m' x a = tablePoint m x a := by
  apply table_point_of_words
  intro k hk
  exact wd_frame1 h hx ho (by omega_using [ha, hk]) (by omega_using [hsep, hk])

theorem CopyKeep.high {x : BitVec 32} {s t : State} (h : CopyKeep x 64 128 s t)
    (hc : Ctx x s) (i : Slot) (hi : 4 ≤ i.val) : env t.mem x i = env s.mem x i := by
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h.frame hc.fit (by decide) (by simp only [offset]; omega_using [])
    (Or.inr (by simp only [offset]; omega_using [hi]))

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.PointPowers`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.X86.PointPowersFrame`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.PointTableAddr`. -/
section
/-! A public table index is multiplied by the point's 128 bytes. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tableAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (off j : Nat)
    (hj : j < 2 ^ 25) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr off)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (off + 128 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  have hv : s₃.gpr .eax = BitVec.ofNat 32 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    change v s₃ .eax = _
    rw [h₃.eax]
    simp only [v, h₂.other .eax (by decide), h₁.gpr, hb, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega_using [hj])]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm j 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * j)) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * j) off]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointLoop`. -/

/-! Frames for public counters, arithmetic and point tables. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def PowersFrame (x : BitVec 32) (s : State) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [sub x 24 4, sub x 64 960, sub x o n, callStk s] m m'

structure PowersKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : PowersFrame x s o n s.mem t.mem

theorem PowersKeep.of_ikeep {x : BitVec 32} {s t : State} (h : IKeep x s t) (o n : Nat) :
    PowersKeep x o n s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp only [true_or, or_true]⟩

theorem workspace_table {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (hlo : 1024 ≤ o) (ho : o + 128 ≤ 8192) :
    tablePoint t.mem x o = tablePoint s.mem x o :=
  table_point_of_words fun k hk => wd_frame1s hc h.frame (by decide) (by omega_using [ho, hk]) (Or.inr (by omega_using [hlo]))

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointPowersCounter`. -/

/-! Write the current point, then advance one or sixteen doublings. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem IKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    IKeep x s t := ⟨h.edi, h.esp, h.rd, h.wr, by rw [hm]; exact Frame.refl _ _⟩

end VG.Proof.Ed25519.X86

end

end

/-! Load a table point while preserving the accumulator for selection. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    FieldKeep x s t := ⟨h, by rw [hm]; exact Frame.refl _ _⟩

theorem FieldKeep.of_copy {x : BitVec 32} {s t : State} (h : CopyKeep x 64 128 s t)
    (hc : Ctx x s) : FieldKeep x s t :=
  ⟨⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr⟩,
    frameWiden h.frame hc.fit (by decide) (by decide) (by decide)⟩

end VG.Proof.Ed25519.X86
