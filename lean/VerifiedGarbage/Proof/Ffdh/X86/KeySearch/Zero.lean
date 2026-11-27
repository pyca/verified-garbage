module

public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86.Spill

/-! ### `Ffdh.X86.KeySearch.Words`, which this module and modules that import it used -/

section

/-! # The key search's state words (x86)

The controller keeps its words in the 128-byte state, at `addr S d`:
reading one through a store to another (`readW_write`), and through writes
apart from the state (`readW_frame`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86

/-- The state's region. -/
abbrev stR (S : BitVec 32) : Region := ⟨S.setWidth 64, 128⟩

/-- A store to the state's word at `d`, read at `e`. -/
theorem readW_write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d e : Nat} (v : BitVec 32)
    (hd : d + 4 ≤ 128) (he : e + 4 ≤ 128) (hde : d = e ∨ d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr S d) v).readW (addr S e) 32 = if d = e then v else m.readW (addr S e) 32 := by
  rw [Spill.addr_eq_of hS hd, Spill.addr_eq_of hS he]
  split
  · subst e; exact Mem.readW_writeW_self32 _ _ _
  · refine Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_using [he]) (by omega_using [hd])) (by decide)

/-- The state's word at `d` lies in the state. -/
theorem contains_addr {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 128) :
    (stR S).Contains (addr S d) 4 := by
  rw [Spill.addr_eq_of hS hd]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

/-- A word of the state, through writes apart from it. -/
theorem readW_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {S : BitVec 32}
    (hS : S.toNat + 128 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (stR S).Disjoint r) {d : Nat} (hd4 : d + 4 ≤ 128) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 :=
  h.readW (contains_addr hS hd4) hd (by decide)

/-- Bytes apart from the regions a frame names. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => h.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## Words by their offsets -/

/-- The state's words at the offsets `ds` hold `f` of their offsets. -/
def Ctl (m : Mem) (S : BitVec 32) (ds : List Nat) (f : Nat → BitVec 32) : Prop :=
  ∀ d ∈ ds, m.readW (addr S d) 32 = f d

/-- Offsets of whole words in the state. -/
def Aligned (ds : List Nat) : Prop := ∀ d ∈ ds, d + 4 ≤ 128 ∧ d % 4 = 0

instance (ds : List Nat) : Decidable (Aligned ds) := inferInstanceAs (Decidable (∀ d ∈ ds, _))

/-- `f` with `v` at `d`. -/
def upd (f : Nat → BitVec 32) (d : Nat) (v : BitVec 32) : Nat → BitVec 32 := fun e => if e = d then v else f e

theorem Ctl.get {m : Mem} {S : BitVec 32} {ds : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f) {d : Nat}
    (hd : d ∈ ds) : m.readW (addr S d) 32 = f d := h d hd

theorem Ctl.congr {m : Mem} {S : BitVec 32} {ds : List Nat} {f g : Nat → BitVec 32} (h : Ctl m S ds f)
    (e : ∀ d ∈ ds, f d = g d) : Ctl m S ds g := fun d hd => (h d hd).trans (e d hd)

/-- A store to a word of the state. -/
theorem Ctl.write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S ds (upd f d v) := by
  intro e he
  obtain ⟨he1, he4⟩ := hA e he
  rw [readW_write hS v hd he1 (by omega_using [hd4, he4])]
  unfold upd
  by_cases hde : d = e
  · subst hde; simp
  · rw [ite_eq_right hde, ite_eq_right (Ne.symm hde)]; exact h e he

/-- Writes apart from the state. -/
theorem Ctl.frame {m m' : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR S).Disjoint r) : Ctl m' S ds f := fun e he => by
  rw [readW_frame hf hS hd (hA e he).1]; exact h e he

end VG.Proof.Ffdh.X86.KeySearch

end

end

/-! # Zeros at an output (x86)

`zeroOut d` writes `p_len` zeros at the pointer in the state's word at `d`,
one byte at a time: a step of its loop (`zeroStep_ok`) keeps its invariant
(`ZInv`), changing only `eax`, `ecx` and `edx`.
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
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega_using [hb, hk])
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    ⟨_, by rw [I.keeps.2.2]; exact hR, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk])⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk]))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega_using [hk])]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega_using [hb, hk, hi]) (by omega_using [hb, hk]) hik)]
      exact I.zero i (by omega_using [hi, hik])
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_using [hn]) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

end VG.Proof.Ffdh.X86.KeySearch
