import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.TCB.X86.Target

/-!
# X448 on x86 (32-bit): the field functions' arguments

A field function (`vg_gf448_r16_*`, `Impl/X448/X86.lean`) reads its
arguments from the stack: the working space and the offsets. `ArgArea s base
n` says what it knows of the first `n` of them on entry: they are readable
and lie outside the working space at `base`, so that what the function
writes there leaves them alone (`ArgArea.keep`).
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The first `n` arguments: readable, and outside the working space at `base`. -/
structure ArgArea (s : State) (base : Addr) (n : Nat) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (argAddr s i) 4
  out : ∀ i < n, ∀ k < 4, 8192 ≤ ofs base (argAddr s i + BitVec.ofNat 64 k)

theorem argOp_ea (s : State) (i : Nat) : s.ea (argOp i) = argAddr s i := rfl

/-- The arguments stay readable and unchanged while the code changes only
registers but `esp`, and memory in the working space. -/
theorem ArgArea.keep {s t : State} {base : Addr} {n : Nat} (h : ArgArea s base n)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : Outside base 0 8192 s.mem t.mem) :
    ArgArea t base n ∧ ∀ i < n, arg t i = arg s i := by
  have ea : ∀ i, argAddr t i = argAddr s i := fun i => by simp only [argAddr, hsp]
  refine ⟨⟨fun i hi => by rw [ea, hrd, hwr]; exact h.read i hi,
    fun i hi k hk => by rw [ea]; exact h.out i hi k hk⟩, fun i hi => ?_⟩
  simp only [arg, ea]
  exact (Mem.readW_congr fun k hk => (hm _ (Or.inr (h.out i hi k hk))).symm).symm

/-- Loading argument `i`. -/
theorem ArgArea.load {s : State} {base : Addr} {n : Nat} (h : ArgArea s base n) {i : Nat} (hi : i < n)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t r (arg s i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem (argOp i)) :: is)) s Q :=
  wp_load (argOp_ea s i) (h.read i hi) k

/-- The address `[r + k]`, for `r` pointing `d` bytes into the working space. -/
theorem Scr.ea_ptr {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d k : Nat}
    (hr : s.gpr r = s.gpr .edi + BitVec.ofNat 32 d) (hdk : d + k < 8192) :
    s.ea (at_ r k) = off base (d + k) := by
  change (s.gpr r + BitVec.ofNat 32 k).setWidth 64 = _
  rw [hr, Offset.add_add]
  exact hs.ea hdk

/-- An offset plus the working space, as `add r, edi` computes it. -/
theorem ofNat_add_edi {s : State} {d k : Nat} {p : BitVec 32}
    (hp : p = s.gpr .edi + BitVec.ofNat 32 k) :
    BitVec.ofNat 32 d + p = s.gpr .edi + BitVec.ofNat 32 (k + d) := by
  rw [hp, BitVec.add_comm, Offset.add_add]

end VG.Proof.X448.X86
