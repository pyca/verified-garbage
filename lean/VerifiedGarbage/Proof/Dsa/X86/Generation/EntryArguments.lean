module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Incoming arguments remain readable above both persistent stack frames -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure EntryArguments (base : Addr) (args : Nat → BitVec 32) (s : State) : Prop where
  frame : SearchFrame s base
  bound : base.toNat + 216 ≤ 2 ^ 32
  read : ∀ j < 12, InRegions (s.rd ++ s.wr) (off base (168 + 4 * j)) 4
  value : ∀ j < 12, s.mem.readW (off base (168 + 4 * j)) 32 = args j

theorem EntryArguments.source {base : Addr} {args : Nat → BitVec 32} {s : State}
    (R : EntryArguments base args s) {j : Nat} (hj : j < 12) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp (168 + 4 * j))) = some (args j) := by
  have ea : s.ea (VG.Impl.Mont.X86.at_ .esp (168 + 4 * j)) = off base (168 + 4 * j) := by
    change addr (s.gpr .esp) (168 + 4 * j) = _
    rw [addr_eq (by have := R.bound; have := R.frame.esp_toNat; omega), R.frame.esp]
  change s.load32 _ = _
  rw [ea, State.load32, ite_eq_left (R.read j hj), R.value j hj]

theorem EntryArguments.keep {base : Addr} {args : Nat → BitVec 32} {s t : State} {rs : List Reg}
    (R : EntryArguments base args s) (O : Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem)
    (K : Keeps rs s t) (sp : .esp ∉ rs) : EntryArguments base args t := by
  refine ⟨R.frame.keeps K sp, R.bound, ?_, ?_⟩
  · intro j hj; rw [K.2.1, K.2.2]; exact R.read j hj
  · intro j hj
    refine (O.readW (r := ⟨off base (168 + 4 * j), 4⟩) ?_ ?_ (by decide)).trans (R.value j hj)
    · simpa only [off, BitVec.add_zero] using
        (Offset.contains_base (off base (168 + 4 * j)) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; omega) (by omega)

def incomingWords (args W : Nat → BitVec 32) (pairs : List (Nat × Nat)) : Nat → BitVec 32 :=
  pairs.foldl (fun words pair => frameUpdate words pair.2 (args pair.1)) W

theorem entryIncomingPair_ok {base : Addr} {args W : Nat → BitVec 32} {s : State} {j slot : Nat}
    (R : EntryArguments base args s) (words : FrameWords s.mem base W) (hj : j < 12) (hs : slot < 37) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.at_ .esp (168 + 4 * j))), .store (frameSlot slot) .eax]) s
      fun t => EntryArguments base args t ∧ FrameWords t.mem base (frameUpdate W slot (args j)) ∧
        Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine wp_movS (R.source hj) fun a sa _ => ?_
  have F := R.frame.keeps sa.keeps (by decide)
  refine wp_storeS (F.ea hs) (F.writable hs) fun t at' => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off base (4 * slot)) (args j) := by rw [at'.mem, sa.gpr, sa.mem]
  have O : Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem := by
    rw [mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; omega) (by omega))
  have K := sa.keeps.trans (at'.keeps [.eax])
  exact ⟨R.keep O K (by decide), by rw [mem]; exact words.write hs _, O, K⟩

theorem entryIncomingList_ok {base : Addr} {args W : Nat → BitVec 32} {s : State} (pairs : List (Nat × Nat))
    (R : EntryArguments base args s) (words : FrameWords s.mem base W)
    (bounds : ∀ pair ∈ pairs, pair.1 < 12 ∧ pair.2 < 37) :
    WP isa (.block (pairs.flatMap fun (j, slot) =>
      [.mov .eax (.mem (VG.Impl.Mont.X86.at_ .esp (168 + 4 * j))), .store (frameSlot slot) .eax])) s
      fun t => EntryArguments base args t ∧ FrameWords t.mem base (incomingWords args W pairs) ∧
        Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction pairs generalizing s W with
  | nil => exact WP.block_nil ⟨R, words, Frame.refl _ _, Keeps.refl _ _⟩
  | cons pair rest ih =>
    obtain ⟨j, slot⟩ := pair
    have h := bounds (j, slot) List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (entryIncomingPair_ok R words h.1 h.2) fun a ⟨Ra, Wa, Oa, Ka⟩ => ?_)
    refine WP.mono (ih Ra Wa (fun pair hp => bounds pair (List.mem_cons_of_mem _ hp))) fun t ⟨Rt, Wt, Ot, Kt⟩ => ?_
    exact ⟨Rt, Wt, Oa.trans Ot, Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
